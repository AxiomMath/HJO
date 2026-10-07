/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.LhsOpShiftAmbient
public import HJO.Shuffle.LhsOpDefs

/-!
# Mellit's `S`-step on the whole stage word

For coprime `m, n ≥ 1`, the operator `τ^*τ` transports `lhsOp m (n+m) α` along `lhsOp m n α`, with
no sign.

Mellit's `S`-step is the identity `Φ_kS(L) = LΦ_k` for `Φ_k = τ^*_kτ_k` on every `V_k`, where `S`
fixes `y_1`, `T_i`, `d_-` and sends `d^*_+ ↦ -y_1d^*_+`. With `π_k = y_1⋯y_k` and the
renormalisation `Ψ_k = π_k·Φ_k`, an operator `W` at `(m,n)` from level `k` to level `k'` and an
operator `E` at `(m,n+m)` are *paired* when there is a polynomial operator `X` of fixed degree `c`
with

* `X(π_k G) = π_{k'} W G` for every `G`, and
* `Ψ_{k'}(EF) = X̂(Ψ_kF)` for every `F`.

Pairing is closed under products, sums and scalar multiples, and holds for the generators `y_1`,
`T_i^{±1}`, `d_-` (paired with themselves) and `d^*_+` (paired with `-y_1d^*_+`), hence for `z_1`
paired with `-y_1z_1`. The shear `β_{m,n+m} = 𝗒·β_{m,n}[𝗓 ↦ 𝗓𝗒]` of slope words extends it to the
stage letters, the stages, the stage word and `lowerRun`. At level `0` we have `π_0 = 1` and
`Ψ_0 = τ^*τ` on constants.

## Main definitions

* `HJO.Mellit.LhsShift.yProd`: the product `π_k = y_1⋯y_k`.
* `HJO.Mellit.LhsShift.Pairs`: the pairing of an operator `W` with an operator `E` from level `k`
  to level `k'` through a partner of degree `c`.
* `HJO.Mellit.LhsShift.letterW`, `HJO.Mellit.LhsShift.letterE`: the operators substituted for the
  letters of a slope word, and their `S`-images.

## Main results

* `HJO.Mellit.LhsShift.pairs_zop`: `z_1` is paired with `-y_1z_1`.
* `HJO.Mellit.LhsShift.slopeOperator_add_self`: the slope operator at `(m,n+m)` in terms of the
  `S`-images of the letters of the slope word of `(m,n)`.
* `HJO.Mellit.LhsShift.pairs_stageFromEnd`: the stage word at `(m,n)` is paired with the stage word
  at `(m,n+m)`.
* `HJO.Mellit.LhsShift.nsTransports_lhsOp_add_self`: `τ^*τ` transports `lhsOp q u m (n+m) α` along
  `lhsOp q u m n α` whenever `q` and `u` are not roots of unity.
* `HJO.Mellit.LhsDesign.lhsOp_add_self`: the same statement at the standing parameters.

## Implementation notes

The operator `Φ_k` involves the factor `∏_{i ≤ k}(1-y_i^{-1})`, which requires a localisation.
Its renormalisation `Ψ_k = π_k·Φ_k` lives in the completion of the total space itself, at the cost
of conjugating every generator by `π_k`.

## References

* A. Mellit, *Toric braids and `(m,n)`-parking functions*, §3.7.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Mellit.LhsShift

open HJO.Sweep

section YProd

variable {L : Type*} [Field L]

/-- `π_k = y_1⋯y_k`. -/
noncomputable def yProd (L : Type*) [Field L] (k : ℕ) : Total L :=
  ∏ i ∈ range k, (auxVar (i + 1) : Total L)

/-- `π_0 = 1`. -/
theorem yProd_zero : yProd L 0 = 1 := by rw [yProd, Finset.prod_range_zero]

/-- `π_{k+1} = π_k·y_{k+1}`. -/
theorem yProd_succ (k : ℕ) : yProd L (k + 1) = yProd L k * (auxVar (k + 1) : Total L) := by
  rw [yProd, yProd, Finset.prod_range_succ]

/-- `π_k` lies in the piece `V_k`. -/
theorem yProd_mem_piece (k : ℕ) : yProd L k ∈ piece L k :=
  Subalgebra.prod_mem _ fun i hi =>
    auxVar_mem_piece (by omega) (by rw [Finset.mem_range] at hi; omega)

/-- `π_k` is fixed by `qshiftNeg q m`. -/
theorem qshiftNeg_yProd (q : L) (m k : ℕ) : qshiftNeg q m (yProd L k) = yProd L k := by
  rw [yProd, map_prod]
  exact Finset.prod_congr rfl fun i _ => qshiftNeg_auxVar_apply q m _

/-- `π_k` is fixed by the swap `swapAux L i` of `y_i` and `y_{i+1}`, for `1 ≤ i` and
`i + 1 ≤ k`. -/
theorem swapAux_yProd {i k : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k) :
    swapAux L i (yProd L k) = yProd L k := by
  rw [yProd, map_prod]
  refine Finset.prod_equiv (Equiv.swap (i - 1) i) (fun m => ?_) (fun m _ => ?_)
  · simp only [Finset.mem_range, Equiv.swap_apply_def]
    split_ifs <;> omega
  · rw [auxVar, Nat.add_sub_cancel, swapAux_X, auxVar, Nat.add_sub_cancel]

/-- `y_1·d^*_+(π_k) = π_{k+1}`. -/
theorem dplusStar_yProd [Algebra ℚ L] (q u : L) (k : ℕ) :
    (auxVar 1 : Total L) * dplusStar q u k (yProd L k) = yProd L (k + 1) := by
  rw [← dplusStarAlg_eq_dplusStar, yProd, map_prod, yProd, Finset.prod_range_succ', mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [dplusStarAlg_auxVar q u (by omega) (by omega)]

end YProd

section Pairs

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- `W` and `E` are paired from level `k` to level `k'` with degree `c`: there is an operator `X`
shifting degree by `c` with `X(π_k G) = π_{k'} W G` for every `G` and `Ψ_{k'}(EF) = X̂(Ψ_kF)` for
every `F`. -/
def Pairs (q u : L) (k k' : ℕ) (c : ℤ) (W E : Module.End L (Total L)) : Prop :=
  ∃ X : Module.End L (Total L), IsHom c X ∧
    (∀ G : Total L, X (yProd L k * G) = yProd L k' * W G) ∧
    ∀ F : Total L, ExtRel X c (psiAmb q u k' (E F)) (psiAmb q u k F)

/-- Pairing is compatible with composition, the degrees adding. -/
theorem Pairs.mul {k k' k'' : ℕ} {c₁ c₂ : ℤ} {W₁ W₂ E₁ E₂ : Module.End L (Total L)}
    (h₁ : Pairs q u k' k'' c₁ W₁ E₁) (h₂ : Pairs q u k k' c₂ W₂ E₂) :
    Pairs q u k k'' (c₁ + c₂) (W₁ * W₂) (E₁ * E₂) := by
  obtain ⟨X₁, hX₁, hc₁, he₁⟩ := h₁
  obtain ⟨X₂, hX₂, hc₂, he₂⟩ := h₂
  refine ⟨X₁ * X₂, hX₁.mul hX₂, fun G => ?_, fun F => (he₁ (E₂ F)).comp (he₂ F) hX₂⟩
  rw [Module.End.mul_apply, hc₂, hc₁]
  rfl

/-- Pairing is compatible with sums at common levels and degree. -/
theorem Pairs.add {k k' : ℕ} {c : ℤ} {W₁ W₂ E₁ E₂ : Module.End L (Total L)}
    (h₁ : Pairs q u k k' c W₁ E₁) (h₂ : Pairs q u k k' c W₂ E₂) :
    Pairs q u k k' c (W₁ + W₂) (E₁ + E₂) := by
  obtain ⟨X₁, hX₁, hc₁, he₁⟩ := h₁
  obtain ⟨X₂, hX₂, hc₂, he₂⟩ := h₂
  refine ⟨X₁ + X₂, hX₁.add hX₂, fun G => ?_, fun F => ?_⟩
  · rw [LinearMap.add_apply, hc₁, hc₂, LinearMap.add_apply, mul_add]
  · rw [LinearMap.add_apply, psiAmb_add]
    exact (he₁ F).add (he₂ F)

/-- Pairing is compatible with scalar multiplication. -/
theorem Pairs.smul {k k' : ℕ} {c : ℤ} {W E : Module.End L (Total L)} (r : L)
    (h : Pairs q u k k' c W E) : Pairs q u k k' c (r • W) (r • E) := by
  obtain ⟨X, hX, hc, he⟩ := h
  refine ⟨r • X, hX.smul r, fun G => ?_, fun F => ?_⟩
  · rw [LinearMap.smul_apply, hc, LinearMap.smul_apply, mul_smul_comm]
  · rw [LinearMap.smul_apply, psiAmb_smul]
    exact (he F).smul r

/-- Pairing is invariant under equalities of the degree and of the two operators. -/
theorem Pairs.congr {k k' : ℕ} {c c' : ℤ} {W W' E E' : Module.End L (Total L)}
    (h : Pairs q u k k' c W E) (hc : c = c') (hW : W = W') (hE : E = E') :
    Pairs q u k k' c' W' E' := hc ▸ hW ▸ hE ▸ h

/-- Pairing is compatible with negation. -/
theorem Pairs.neg {k k' : ℕ} {c : ℤ} {W E : Module.End L (Total L)}
    (h : Pairs q u k k' c W E) : Pairs q u k k' c (-W) (-E) :=
  (h.smul (-1 : L)).congr rfl (neg_one_smul L W) (neg_one_smul L E)

/-- Pairing is compatible with differences at common levels and degree. -/
theorem Pairs.sub {k k' : ℕ} {c : ℤ} {W₁ W₂ E₁ E₂ : Module.End L (Total L)}
    (h₁ : Pairs q u k k' c W₁ E₁) (h₂ : Pairs q u k k' c W₂ E₂) :
    Pairs q u k k' c (W₁ - W₂) (E₁ - E₂) :=
  (h₁.add h₂.neg).congr rfl (sub_eq_add_neg W₁ W₂).symm (sub_eq_add_neg E₁ E₂).symm

/-- The identity is paired with itself at every level, with degree `0`. -/
theorem pairs_one (k : ℕ) : Pairs q u k k 0 1 1 :=
  ⟨1, isHom_one, fun G => rfl, fun F n => by
    rw [extT, ite_eq_left (by omega), sub_zero, Int.toNat_natCast]
    rfl⟩

/-- If `W` and `E` are paired at level `k` with degree `c`, then `W ^ n` and `E ^ n` are paired
with degree `n * c`. -/
theorem Pairs.pow {k : ℕ} {c : ℤ} {W E : Module.End L (Total L)} (h : Pairs q u k k c W E)
    (n : ℕ) : Pairs q u k k ((n : ℤ) * c) (W ^ n) (E ^ n) := by
  induction n with
  | zero => exact (pairs_one k).congr (by simp) (pow_zero W).symm (pow_zero E).symm
  | succ n ih =>
    exact (ih.mul h).congr (by push_cast; ring) (pow_succ W n).symm (pow_succ E n).symm

/-- A product of operators each paired with itself at level `k` with degree `0` is paired with
itself with degree `0`. -/
theorem pairs_listProd {k : ℕ} (l : List (Module.End L (Total L)))
    (h : ∀ T ∈ l, Pairs q u k k 0 T T) : Pairs q u k k 0 l.prod l.prod := by
  induction l with
  | nil => exact pairs_one k
  | cons T l ih =>
    rw [List.prod_cons]
    exact ((h T (List.mem_cons_self ..)).mul
      (ih fun T' hT' => h T' (List.mem_cons_of_mem T hT'))).congr (by ring) rfl rfl

/-! ### The generators -/

/-- Multiplication by `y_1` is paired with itself at every level, with degree `1`. -/
theorem pairs_auxVar_one (k : ℕ) :
    Pairs q u k k 1 (LinearMap.mulLeft L (auxVar 1 : Total L))
      (LinearMap.mulLeft L (auxVar 1 : Total L)) :=
  ⟨LinearMap.mulLeft L (auxVar 1 : Total L),
    by simpa using isHom_mulLeft (auxVar_mem_totalComp L 1),
    fun G => by rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, mul_left_comm],
    fun F => extRel_psiAmb_auxVar_one q u k F⟩

/-- `T_i` is paired with itself at level `k` with degree `0`, for `1 ≤ i` and `i + 1 ≤ k`. -/
theorem pairs_braid {i k : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k) :
    Pairs q u k k 0 (braidEnd q i) (braidEnd q i) :=
  ⟨braidEnd q i, isHom_braidEnd q i,
    fun G => braid_symmetric_mul q (swapAux_yProd hi hik) G,
    fun F => extRel_psiAmb_braid q u hi hik F⟩

/-- `T_i^{-1}` is paired with itself at level `k` with degree `0`, for `1 ≤ i` and
`i + 1 ≤ k`. -/
theorem pairs_braidInv {i k : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k) :
    Pairs q u k k 0 (braidInvEnd q i) (braidInvEnd q i) :=
  ⟨braidInvEnd q i, isHom_braidInvEnd q i,
    fun G => braidInv_symmetric_mul q (swapAux_yProd hi hik) G,
    fun F => extRel_psiAmb_braidInv q u hi hik F⟩

/-- If `q` and `u` are not roots of unity, `d^*_+` is paired with `-y_1d^*_+` from level `k` to
level `k + 1`, with degree `1`. -/
theorem pairs_dplusStar (hq : ∀ r : ℕ, 1 ≤ r → q ^ r ≠ 1) (hu : ∀ r : ℕ, 1 ≤ r → u ^ r ≠ 1)
    (k : ℕ) :
    Pairs q u k (k + 1) 1 (dplusStar q u k)
      (-(LinearMap.mulLeft L (auxVar 1 : Total L) * dplusStar q u k)) := by
  have hY : IsHom 1 (LinearMap.mulLeft L (auxVar 1 : Total L)) := by
    simpa using isHom_mulLeft (auxVar_mem_totalComp L 1)
  refine ⟨LinearMap.mulLeft L (auxVar 1 : Total L) * dplusStar q u k,
    by simpa using hY.mul (isHom_dplusStar q u k), fun G => ?_, fun F => ?_⟩
  · rw [Module.End.mul_apply, LinearMap.mulLeft_apply, ← dplusStarAlg_eq_dplusStar, map_mul,
      dplusStarAlg_eq_dplusStar, dplusStarAlg_eq_dplusStar, ← mul_assoc, dplusStar_yProd]
  · have h := ((extRel_psiAmb_auxVar_one q u (k + 1) (dplusStar q u k F)).comp
      (extRel_psiAmb_dplusStar q u hq hu k F) (by simpa using (isHom_dplusStar q u k).neg)).neg
    refine h.congr ?_ ?_
    · rw [LinearMap.neg_apply, Module.End.mul_apply, LinearMap.mulLeft_apply, psiAmb_neg]
    · exact LinearMap.ext fun G => by
        rw [LinearMap.neg_apply, Module.End.mul_apply, LinearMap.neg_apply, LinearMap.mulLeft_apply,
          Module.End.mul_apply, LinearMap.mulLeft_apply]
        rw [mul_neg (auxVar 1 : Total L), neg_neg]

/-- If `q` is not a root of unity, `d_-` is paired with itself from level `k + 1` to level `k`,
with degree `-1`, through the partner `dminusDown = d_- ∘ y_{k+1}^{-1}`. -/
theorem pairs_dminus (hq : ∀ r : ℕ, 1 ≤ r → q ^ r ≠ 1) (k : ℕ) :
    Pairs q u (k + 1) k (-1) (dminus q (k + 1)) (dminus q (k + 1)) :=
  ⟨dminusDown q (k + 1), isHom_dminusDown q (k + 1),
    fun G => by
      rw [yProd_succ, mul_assoc, dminusDown_mul_of_mem_piece q (yProd_mem_piece k)
        (qshiftNeg_yProd q (k + 1) k), dminusDown_auxVar_mul],
    fun F => extRel_psiAmb_dminus q u hq k F⟩

/-! ### The trains -/

/-- The ascending word in the `T_i` from `a` to `b` is paired with itself at level `k` with degree
`0`, for `1 ≤ a` and `b ≤ k`. -/
theorem pairs_ascendingWord_braid {k a b : ℕ} (ha : 1 ≤ a) (hb : b ≤ k) :
    Pairs q u k k 0 (Braid.ascendingWord (braidEnd q) a b)
      (Braid.ascendingWord (braidEnd q) a b) := by
  rw [Braid.ascendingWord]
  refine pairs_listProd _ fun T hT => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hT
  rw [List.mem_range'_1] at hi
  exact pairs_braid (by omega) (by omega)

/-- The ascending word in the `T_i^{-1}` from `a` to `b` is paired with itself at level `k` with
degree `0`, for `1 ≤ a` and `b ≤ k`. -/
theorem pairs_ascendingWord_braidInv {k a b : ℕ} (ha : 1 ≤ a) (hb : b ≤ k) :
    Pairs q u k k 0 (Braid.ascendingWord (braidInvEnd q) a b)
      (Braid.ascendingWord (braidInvEnd q) a b) := by
  rw [Braid.ascendingWord]
  refine pairs_listProd _ fun T hT => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hT
  rw [List.mem_range'_1] at hi
  exact pairs_braidInv (by omega) (by omega)

/-- The descending word in the `T_i` from `a` to `b` is paired with itself at level `k` with degree
`0`, for `1 ≤ b` and `a ≤ k`. -/
theorem pairs_descendingWord_braid {k a b : ℕ} (hb : 1 ≤ b) (ha : a ≤ k) :
    Pairs q u k k 0 (Braid.descendingWord (braidEnd q) a b)
      (Braid.descendingWord (braidEnd q) a b) := by
  rw [Braid.descendingWord]
  refine pairs_listProd _ fun T hT => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hT
  rw [List.mem_reverse, List.mem_range'_1] at hi
  exact pairs_braid (by omega) (by omega)

/-- The descending word in the `T_i^{-1}` from `a` to `b` is paired with itself at level `k` with
degree `0`, for `1 ≤ b` and `a ≤ k`. -/
theorem pairs_descendingWord_braidInv {k a b : ℕ} (hb : 1 ≤ b) (ha : a ≤ k) :
    Pairs q u k k 0 (Braid.descendingWord (braidInvEnd q) a b)
      (Braid.descendingWord (braidInvEnd q) a b) := by
  rw [Braid.descendingWord]
  refine pairs_listProd _ fun T hT => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hT
  rw [List.mem_reverse, List.mem_range'_1] at hi
  exact pairs_braidInv (by omega) (by omega)

/-- The upward train from `a` to `b` is paired with itself at level `k` with degree `0`, for
`1 ≤ a, b ≤ k`. -/
theorem pairs_trainUpEnd {k a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hak : a ≤ k) (hbk : b ≤ k) :
    Pairs q u k k 0 (trainUpEnd q a b) (trainUpEnd q a b) := by
  rw [trainUpEnd, Braid.trainUp]
  split_ifs
  · exact pairs_ascendingWord_braid ha hbk
  · exact pairs_descendingWord_braidInv hb hak

/-- The downward train from `a` to `b` is paired with itself at level `k` with degree `0`, for
`1 ≤ a, b ≤ k`. -/
theorem pairs_trainDownEnd {k a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hak : a ≤ k) (hbk : b ≤ k) :
    Pairs q u k k 0 (trainDownEnd q a b) (trainDownEnd q a b) := by
  rw [trainDownEnd, Braid.trainDown]
  split_ifs
  · exact pairs_descendingWord_braid hb hak
  · exact pairs_ascendingWord_braidInv ha hbk

/-! ### `z_1`, whose `S`-image is `-y_1z_1` -/

/-- If `q` and `u` are not roots of unity, `z_1` is paired with `-y_1z_1` at level `j + 1`, with
degree `0`. -/
theorem pairs_zop (hq : ∀ r : ℕ, 1 ≤ r → q ^ r ≠ 1) (hu : ∀ r : ℕ, 1 ≤ r → u ^ r ≠ 1)
    (j : ℕ) :
    Pairs q u (j + 1) (j + 1) 0 (zopOneStar q u (j + 1))
      (-(LinearMap.mulLeft L (auxVar 1 : Total L) * zopOneStar q u (j + 1))) := by
  have P1 := (pairs_dplusStar (q := q) (u := u) hq hu j).mul (pairs_dminus hq j)
  have P2 := (pairs_dminus (q := q) (u := u) hq (j + 1)).mul (pairs_dplusStar hq hu (j + 1))
  have P := ((P1.sub (P2.congr (by ring) rfl rfl)).mul
    (pairs_trainUpEnd (q := q) (u := u) (k := j + 1) (a := j + 1) (b := 1) (by omega) le_rfl
      le_rfl (by omega))).smul (q ^ (j + 1) / (1 - q))
  refine P.congr (by ring) ?_ ?_
  · rw [zopOneStar, Nat.add_sub_cancel]
  · refine LinearMap.ext fun F => ?_
    rw [zopOneStar, Nat.add_sub_cancel]
    simp only [LinearMap.smul_apply, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.neg_apply, LinearMap.mulLeft_apply, map_neg,
      dminus_auxVar_mul q (k := j + 1) (j := 1) le_rfl (by omega)]
    rw [Algebra.smul_def, Algebra.smul_def]
    ring

end Pairs

/-! ### The slope word, sheared -/

section Words

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

open HJO.Mellit (SlopeLetter)

/-- The operator substituted for a letter of a slope word: `-y_1` for `y` and `(qu)^{-1}z_1` for
`z`. -/
noncomputable def letterW (q u : L) (k : ℕ) : SlopeLetter → Module.End L (Total L)
  | .y => -LinearMap.mulLeft L (auxVar 1 : Total L)
  | .z => (q * u)⁻¹ • zop q u k 1

/-- The `S`-image of `letterW`: `-y_1` for `y` and `(qu)^{-1}(-y_1z_1)` for `z`. -/
noncomputable def letterE (q u : L) (k : ℕ) : SlopeLetter → Module.End L (Total L)
  | .y => -LinearMap.mulLeft L (auxVar 1 : Total L)
  | .z => (q * u)⁻¹ • -(LinearMap.mulLeft L (auxVar 1 : Total L) * zop q u k 1)

/-- The slope operator of `(m,n)` is the product of `letterW` over the slope word of `(m,n)`. -/
theorem slopeOperator_eq_prod (q u : L) (k m n : ℕ) :
    slopeOperator q u k m n = ((Mellit.slopeWord m n).map (letterW q u k)).prod := by
  rw [slopeOperator]
  congr 2

/-- If `q` and `u` are not roots of unity, each letter's `letterW` is paired with its `letterE` at
level `j + 1`, with some degree. -/
theorem pairs_letter (hq : ∀ r : ℕ, 1 ≤ r → q ^ r ≠ 1) (hu : ∀ r : ℕ, 1 ≤ r → u ^ r ≠ 1)
    (j : ℕ) (l : SlopeLetter) :
    ∃ c, Pairs q u (j + 1) (j + 1) c (letterW q u (j + 1) l) (letterE q u (j + 1) l) := by
  cases l with
  | y => exact ⟨1, (pairs_auxVar_one (j + 1)).neg⟩
  | z =>
    refine ⟨0, ((pairs_zop hq hu j).smul ((q * u)⁻¹)).congr rfl ?_ ?_⟩
    · change _ = (q * u)⁻¹ • zop q u (j + 1) 1
      rw [zop_one]
    · change _ = (q * u)⁻¹ • -(LinearMap.mulLeft L (auxVar 1 : Total L) * zop q u (j + 1) 1)
      rw [zop_one]

/-- If `q` and `u` are not roots of unity, the product of `letterW` over a word is paired with the
product of `letterE` over it at level `j + 1`, with some degree. -/
theorem pairs_word (hq : ∀ r : ℕ, 1 ≤ r → q ^ r ≠ 1) (hu : ∀ r : ℕ, 1 ≤ r → u ^ r ≠ 1)
    (j : ℕ) : ∀ t : List SlopeLetter, ∃ c, Pairs q u (j + 1) (j + 1) c
      (t.map (letterW q u (j + 1))).prod (t.map (letterE q u (j + 1))).prod := by
  intro t
  induction t with
  | nil => exact ⟨0, pairs_one _⟩
  | cons l t ih =>
    obtain ⟨c₁, h₁⟩ := pairs_letter hq hu j l
    obtain ⟨c₂, h₂⟩ := ih
    exact ⟨c₁ + c₂, (h₁.mul h₂).congr rfl (by simp [List.prod_cons]) (by simp [List.prod_cons])⟩

/-- `-y_1` times the product of `letterW` over the sheared word `w[𝗓 ↦ 𝗓𝗒]` equals the product of
`letterE` over `w` times `-y_1`. -/
theorem letterW_y_mul_shear (q u : L) (k : ℕ) (w : List SlopeLetter) :
    letterW q u k .y * ((w.flatMap Mellit.shiftSubst).map (letterW q u k)).prod
      = (w.map (letterE q u k)).prod * letterW q u k .y := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [List.flatMap_cons, List.map_append, List.prod_append, List.map_cons, List.prod_cons]
    cases a with
    | y =>
      simp only [Mellit.shiftSubst, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one]
      rw [ih, ← mul_assoc]
      rfl
    | z =>
      simp only [Mellit.shiftSubst, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one]
      have hyz : letterW q u k .y * letterW q u k .z = letterE q u k .z := by
        change -LinearMap.mulLeft L (auxVar 1 : Total L) * ((q * u)⁻¹ • zop q u k 1)
          = (q * u)⁻¹ • -(LinearMap.mulLeft L (auxVar 1 : Total L) * zop q u k 1)
        rw [mul_smul_comm]
        congr 1
      rw [mul_assoc, ← mul_assoc (letterW q u k .y), hyz, mul_assoc, ih, ← mul_assoc]

/-- For coprime `m, n ≥ 1`, the slope operator of `(m,n+m)` is the product of `letterE` over the
slope word of `(m,n)`, followed by `-y_1`. -/
theorem slopeOperator_add_self {m n : ℕ} (hc : Nat.Coprime m n) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (q u : L) (k : ℕ) :
    slopeOperator q u k m (n + m)
      = ((Mellit.slopeWord m n).map (letterE q u k)).prod * letterW q u k .y := by
  rw [slopeOperator_eq_prod, Mellit.slopeWord_add_self hc hm hn, List.map_cons, List.prod_cons,
    letterW_y_mul_shear]

/-! ### The stage letters and the stages -/

variable {m n : ℕ}

/-- If `q` and `u` are not roots of unity and `m, n ≥ 1` are coprime, `replOneTotal` at `(m,n)` is
paired with `replOneTotal` at `(m,n+m)` from level `k` to level `k + 1`, with some degree. -/
theorem pairs_replOne (hq : ∀ r : ℕ, 1 ≤ r → q ^ r ≠ 1) (hu : ∀ r : ℕ, 1 ≤ r → u ^ r ≠ 1)
    (hc : Nat.Coprime m n) (hm : 1 ≤ m) (hn : 1 ≤ n) (k : ℕ) :
    ∃ c, Pairs q u k (k + 1) c (Mellit.replOneTotal q u m n k)
      (Mellit.replOneTotal q u m (n + m) k) := by
  obtain ⟨c, hw⟩ := pairs_word hq hu k (Mellit.slopeWord m n)
  have hd := ((pairs_auxVar_one (q := q) (u := u) (k + 1)).mul (pairs_dplusStar hq hu k)).neg
  refine ⟨c + (1 + 1), ((hw.mul hd).smul ((-1 : L) ^ (m - 1))).congr rfl ?_ ?_⟩
  · rw [Mellit.replOneTotal, slopeOperator_eq_prod]
  · rw [Mellit.replOneTotal, slopeOperator_add_self hc hm hn, mul_assoc]
    congr 2

/-- If `q` and `u` are not roots of unity and `m, n ≥ 1` are coprime, `replTwoTotal` at `(m,n)` is
paired with `replTwoTotal` at `(m,n+m)` at level `k + 1`, with some degree. -/
theorem pairs_replTwo (hq : ∀ r : ℕ, 1 ≤ r → q ^ r ≠ 1) (hu : ∀ r : ℕ, 1 ≤ r → u ^ r ≠ 1)
    (hc : Nat.Coprime m n) (hm : 1 ≤ m) (hn : 1 ≤ n) (k : ℕ) :
    ∃ c, Pairs q u (k + 1) (k + 1) c (Mellit.replTwoTotal q u m n k)
      (Mellit.replTwoTotal q u m (n + m) k) := by
  obtain ⟨c, hw⟩ := pairs_word hq hu k (Mellit.slopeWord m n)
  have hz := ((pairs_auxVar_one (q := q) (u := u) (k + 1)).mul (pairs_zop hq hu k)).neg
  refine ⟨c + (1 + 0), ((hw.mul hz).smul ((-1 : L) ^ (m - 1))).congr rfl ?_ ?_⟩
  · rw [Mellit.replTwoTotal, slopeOperator_eq_prod]
  · rw [Mellit.replTwoTotal, slopeOperator_add_self hc hm hn, mul_assoc]
    congr 2

/-- If `q` and `u` are not roots of unity and `m, n ≥ 1` are coprime, `replicatedTotal` at `(m,n)`
is paired with `replicatedTotal` at `(m,n+m)` at level `k + 1`, with some degree. -/
theorem pairs_replicated (hq : ∀ r : ℕ, 1 ≤ r → q ^ r ≠ 1) (hu : ∀ r : ℕ, 1 ≤ r → u ^ r ≠ 1)
    (hc : Nat.Coprime m n) (hm : 1 ≤ m) (hn : 1 ≤ n) (k : ℕ) :
    ∃ c, Pairs q u (k + 1) (k + 1) c (Mellit.replicatedTotal q u m n k)
      (Mellit.replicatedTotal q u m (n + m) k) := by
  obtain ⟨c, h⟩ := pairs_replTwo hq hu hc hm hn k
  refine ⟨0 + c + 0, ((((pairs_trainDownEnd (q := q) (u := u) (k := k + 1) (a := k + 1) (b := 1)
    (by omega) le_rfl le_rfl (by omega)).mul h).mul (pairs_trainUpEnd (q := q) (u := u)
    (k := k + 1) (a := 1) (b := k + 1) le_rfl (by omega) (by omega) le_rfl)).smul
    (q ^ (-(k : ℤ)))).congr rfl ?_ ?_⟩
  · rw [Mellit.replicatedTotal]
  · rw [Mellit.replicatedTotal]

/-- If `q` and `u` are not roots of unity and `m, n ≥ 1` are coprime, the stage `stageTotal` at
`(m,n)` is paired with the stage at `(m,n+m)` from level `k` to level `k + 1`, with some degree. -/
theorem pairs_stage (hq : ∀ r : ℕ, 1 ≤ r → q ^ r ≠ 1) (hu : ∀ r : ℕ, 1 ≤ r → u ^ r ≠ 1)
    (hc : Nat.Coprime m n) (hm : 1 ≤ m) (hn : 1 ≤ n) (k A : ℕ) :
    ∃ c, Pairs q u k (k + 1) c (Mellit.stageTotal q u m n k A)
      (Mellit.stageTotal q u m (n + m) k A) := by
  obtain ⟨c₁, h₁⟩ := pairs_replicated hq hu hc hm hn k
  obtain ⟨c₂, h₂⟩ := pairs_replOne hq hu hc hm hn k
  exact ⟨_, ((h₁.pow (A - 1)).mul ((pairs_trainDownEnd (q := q) (u := u) (k := k + 1)
    (a := k + 1) (b := 1) (by omega) le_rfl le_rfl (by omega)).mul h₂)).congr rfl
    (by rw [Mellit.stageTotal]) (by rw [Mellit.stageTotal])⟩

/-- If `q` and `u` are not roots of unity and `m, n ≥ 1` are coprime, the stage word
`stageFromEnd` of `α` at `(m,n)` is paired with the stage word at `(m,n+m)` from level `k` to level
`k + α.length`, with some degree. -/
theorem pairs_stageFromEnd (hq : ∀ r : ℕ, 1 ≤ r → q ^ r ≠ 1)
    (hu : ∀ r : ℕ, 1 ≤ r → u ^ r ≠ 1) (hc : Nat.Coprime m n) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∀ (α : List ℕ) (k : ℕ), ∃ c, Pairs q u k (k + α.length) c
      (LhsDesign.stageFromEnd q u m n k α) (LhsDesign.stageFromEnd q u m (n + m) k α) := by
  intro α
  induction α with
  | nil => intro k; exact ⟨0, pairs_one k⟩
  | cons A α ih =>
    intro k
    obtain ⟨c₁, h₁⟩ := ih (k + 1)
    obtain ⟨c₂, h₂⟩ := pairs_stage hq hu hc hm hn k A
    have hlen : k + (A :: α).length = k + 1 + α.length := by
      rw [List.length_cons]; ring
    rw [hlen]
    exact ⟨c₁ + c₂, (h₁.mul h₂).congr rfl (by rw [LhsDesign.stageFromEnd])
      (by rw [LhsDesign.stageFromEnd])⟩

/-- If `q` is not a root of unity, `lowerRun q l` is paired with itself from level `l` to level
`0`, with some degree. -/
theorem pairs_lowerRun (hq : ∀ r : ℕ, 1 ≤ r → q ^ r ≠ 1) :
    ∀ l : ℕ, ∃ c, Pairs q u l 0 c (Mellit.lowerRun q l) (Mellit.lowerRun q l) := by
  intro l
  induction l with
  | zero => exact ⟨0, pairs_one 0⟩
  | succ l ih =>
    obtain ⟨c, h⟩ := ih
    exact ⟨c + -1, (h.mul (pairs_dminus hq l)).congr rfl (by rw [Mellit.lowerRun])
      (by rw [Mellit.lowerRun])⟩

end Words

/-! ### Level zero -/

section Zero

variable {L : Type*} [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in
/-- The degree-`e` part of a constant `C h` is the constant on the degree-`e` component of `h`. -/
theorem tproj_C (e : ℕ) (h : Sym.Lambda L) :
    tproj e (MvPolynomial.C h : Total L) = MvPolynomial.C (Sym.lambdaComponent L e h) := by
  refine MvPolynomial.ext _ _ fun m => ?_
  rw [coeff_tproj, MvPolynomial.coeff_C, MvPolynomial.coeff_C]
  split_ifs with hm
  · subst hm
    rw [map_zero, Nat.cast_zero, sub_zero, lcInt, ite_eq_left (by omega), Int.toNat_natCast]
  · rw [map_zero]

/-- At level zero, `Ψ_0` acts on constants as `τ^*τ`: the `e`-th member of `Ψ_0(C g)` is
`C (nsShiftComp q u g e)`. -/
theorem psiAmb_zero_C (q u : L) (g : Sym.Lambda L) (e : ℕ) :
    (psiAmb q u 0 (MvPolynomial.C g) e : Total L)
      = MvPolynomial.C (Sym.nsShiftComp q u g e : Sym.Lambda L) := by
  rw [psiAmb, TotalHat.coe_mul, Sym.nsShiftComp_apply, Sym.coe_nsShiftStar_apply, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [auxProd, Finset.prod_range_zero, one_mul, unitShiftTotal_C, coe_toHat, tproj_C,
    coe_cornerMultiplier_zero, map_mul]

omit [Algebra ℚ L] in
/-- The constant coefficient of an element of `TotalCompInt L e` lies in `LambdaCompInt L e`. -/
theorem constantCoeff_mem_lambdaCompInt {e : ℤ} {G : Total L} (hG : G ∈ TotalCompInt L e) :
    MvPolynomial.constantCoeff G ∈ Sym.LambdaCompInt L e := by
  rcases lt_or_ge e 0 with h | h
  · rw [eq_zero_of_mem_totalCompInt h hG, map_zero]; exact zero_mem _
  · lift e to ℕ using h
    rw [totalCompInt_natCast] at hG
    have h0 := hG 0
    rw [map_zero, Nat.cast_zero, sub_zero] at h0
    exact h0

/-- The operator `lowerRun ∘ stageFromEnd` on constants is `C ∘ lhsOp`. -/
theorem lowerRun_mul_stageFromEnd_C (q u : L) (a b : ℕ) (α : List ℕ) (f : Sym.Lambda L) :
    (Mellit.lowerRun q α.length * LhsDesign.stageFromEnd q u a b 0 α) (MvPolynomial.C f)
      = MvPolynomial.C (LhsDesign.lhsOp q u a b α f) := by
  have hmem : (Mellit.lowerRun q α.length * LhsDesign.stageFromEnd q u a b 0 α)
      (MvPolynomial.C f) ∈ piece L 0 := by
    rw [Module.End.mul_apply, LhsDesign.stageFromEnd_apply]
    refine lowerRun_mem_piece_zero q _ ?_
    simpa [LhsDesign.stageFromEnd_apply] using
      stageFromEnd_mem_piece q u a b α 0 (C_mem_piece_zero f)
  obtain ⟨g, hg⟩ := exists_C_eq_of_mem_piece_zero hmem
  rw [LhsDesign.lhsOp_apply, ← LhsDesign.stageFromEnd_apply, ← Module.End.mul_apply, ← hg,
    MvPolynomial.constantCoeff_C]

omit [Algebra ℚ L] in
/-- If `D` shifts degree both by `c` and by `c'`, then its extensions `extVal c D` and
`extVal c' D` agree. -/
theorem extVal_eq_of_shiftsDegree {c c' : ℤ} {D : Module.End L (Sym.Lambda L)}
    (hD : Sym.ShiftsDegree c D) (hD' : Sym.ShiftsDegree c' D) (G : Sym.LambdaHat L) (e : ℕ) :
    Sym.extVal c D G e = Sym.extVal c' D G e := by
  by_cases hcc : c = c'
  · subst hcc; rfl
  have hD0 : ∀ f, D f = 0 := by
    intro f
    rw [← Sym.sum_lambdaComponent f, map_sum]
    refine Finset.sum_eq_zero fun d _ => ?_
    have h1 := hD d _ (Sym.lambdaComponent_mem L d f)
    have h2 := hD' d _ (Sym.lambdaComponent_mem L d f)
    have e1 := lcInt_of_mem (c' := (d : ℤ) + c) h1
    have e2 := lcInt_of_mem (c' := (d : ℤ) + c) h2
    rw [ite_eq_left rfl] at e1
    rw [ite_eq_right (by omega)] at e2
    rw [← e1, e2]
  unfold Sym.extVal
  split_ifs <;> simp [hD0]

/-- If `q` and `u` are not roots of unity and `m, n ≥ 1` are coprime, `τ^*τ` transports
`lhsOp q u m (n+m) α` along `lhsOp q u m n α`. -/
theorem nsTransports_lhsOp_add_self {q u : L} (hq : ∀ r : ℕ, 1 ≤ r → q ^ r ≠ 1)
    (hu : ∀ r : ℕ, 1 ≤ r → u ^ r ≠ 1) {m n : ℕ} (hmn : Nat.Coprime m n) (hm : 1 ≤ m)
    (hn : 1 ≤ n) (α : List ℕ) {c : ℤ} (hD : Sym.ShiftsDegree c (LhsDesign.lhsOp q u m n α)) :
    Sym.NsTransports q u hD (LhsDesign.lhsOp q u m (n + m) α) := by
  obtain ⟨c₁, h₁⟩ := pairs_lowerRun (q := q) (u := u) hq α.length
  obtain ⟨c₂, h₂⟩ := pairs_stageFromEnd hq hu hmn hm hn α 0
  rw [zero_add] at h₂
  obtain ⟨X, hX, hconj, hext⟩ := h₁.mul h₂
  have hX0 : ∀ G, X G = (Mellit.lowerRun q α.length * LhsDesign.stageFromEnd q u m n 0 α) G :=
    fun G => by simpa [yProd_zero] using hconj G
  have hD' : Sym.ShiftsDegree (c₁ + c₂) (LhsDesign.lhsOp q u m n α) := by
    intro d f hf
    have h := hX d (MvPolynomial.C f) (C_mem_totalComp hf)
    rw [hX0, lowerRun_mul_stageFromEnd_C] at h
    simpa using constantCoeff_mem_lambdaCompInt h
  intro f
  refine Sym.LambdaHat.ext fun e => MvPolynomial.C_injective ℕ (Sym.Lambda L) ?_
  rw [← psiAmb_zero_C, ← lowerRun_mul_stageFromEnd_C, hext (MvPolynomial.C f) e,
    Sym.coe_completionExtension_apply, extVal_eq_of_shiftsDegree hD hD', Sym.extVal, extT]
  split_ifs
  · rw [psiAmb_zero_C, hX0, lowerRun_mul_stageFromEnd_C]
  · rw [map_zero]

end Zero

end HJO.Mellit.LhsShift

namespace HJO.Mellit.LhsDesign

open HJO.Sym HJO.Sweep HJO.Ascent MvPolynomial

variable (K : Type*) [Field K] [Algebra ParamRing K] [IsFractionRing ParamRing K] [Algebra ℚ K]

local notation "𝗊" => paramQ K
local notation "𝗎" => paramU K

/-- At the standing parameters, for coprime `m, n ≥ 1`, `τ^*τ` transports `lhsOp m (n+m) α` along
`lhsOp m n α`, with no sign. -/
theorem lhsOp_add_self {m n : ℕ} (hmn : Nat.Coprime m n) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (α : List ℕ) (_hpos : ∀ x ∈ α, 0 < x) {c : ℤ} (hD : ShiftsDegree c (lhsOp 𝗊 𝗎 m n α)) :
    NsTransports 𝗊 𝗎 hD (lhsOp 𝗊 𝗎 m (n + m) α) :=
  LhsShift.nsTransports_lhsOp_add_self
    (fun r hr => by
      obtain ⟨j, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
      exact HJO.Standing.paramQ_pow_succ_ne_one K j)
    (fun r hr => by
      obtain ⟨j, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
      exact HJO.Standing.paramU_pow_succ_ne_one K j)
    hmn hm hn α hD

end HJO.Mellit.LhsDesign

end
