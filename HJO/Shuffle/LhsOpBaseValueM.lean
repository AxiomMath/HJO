/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.LhsOpDefs

/-! # The base-slope stage word, conjugated into Carlsson--Mellit's original operators

Mellit's operators on `V_*` (the ones of `HJO.Sweep`, `d_-`, `d_+`, `d^*_+`, `z_1`) are a
modification of Carlsson--Mellit's: by Remark 3.1 of A. Mellit, *Toric braids and `(m,n)`-parking
functions*, arXiv:1604.07456, multiplication by `M_k = (-1)^k y_1⋯y_k` on each `V_k` intertwines the
original lowering operator `d_-^{CM} = -d_-y_k` (`HJO.Sweep.dminusCM`) with `d_-`. This file
transports the stage word of `HJO.Mellit.lhsRewrite_sweepWitness` at the slope `(1,1)` along `M`.

At `(1,1)` the two stage letters are `-y_1d^*_+` and `-y_1z_1`, and both become *starred
Carlsson--Mellit operators* under `M`:

* `-y_1d^*_+ ∘ M_k = M_{k+1} ∘ d^*_+`
  (`HJO.Mellit.LhsDesign.neg_auxVar_one_mul_dplusStar_mPoly_mul`);
* `-y_1z_1 ∘ M_{k+1} = M_{k+1} ∘ q^{k+1}/(1-q)·(d^*_+d_-^{CM} - d_-^{CM}d^*_+)T^*_{k+1↘1}`.

So the whole stage word is `M` of a word in `d^*_+`, `d_-^{CM}` and the braid operators
(`HJO.Mellit.LhsDesign.stageTotal_one_one_mPoly_mul`), and the right-hand side of the clause is
`ct(d_-^{CM,ℓ}(⋯))` (`HJO.Mellit.LhsDesign.lhsOp_one_one_apply_one_eq_lowerRunCM`).

## Main definitions

* `HJO.Mellit.LhsDesign.mPoly`: `M_k = (-1)^k y_1⋯y_k`.
* `HJO.Mellit.LhsDesign.lowerRunCM`: `d_-^{CM,ℓ}`.
* `HJO.Mellit.LhsDesign.oldOne`, `oldRep`, `oldStage`, `oldStageFrom`: the conjugated stage.
-/

@[expose] public section

namespace HJO.Mellit.LhsDesign

open HJO.Sweep MvPolynomial

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The two lowering coefficient extractions -/

/-- `lowerCoeff_j(y_{j+1}G) = -lowerCoeffShift_j(G)`. -/
theorem lowerCoeff_X_mul (j : ℕ) (G : Total L) :
    lowerCoeff L j (X j * G) = -lowerCoeffShift L j G := by
  have h : (lowerCoeff L j).comp (LinearMap.mulLeft (Sym.Lambda L) (X j : Total L))
      = -lowerCoeffShift L j := by
    refine (MvPolynomial.basisMonomials ℕ (Sym.Lambda L)).ext fun d => ?_
    have hb : (MvPolynomial.basisMonomials ℕ (Sym.Lambda L)) d = MvPolynomial.monomial d 1 :=
      congrFun (MvPolynomial.coe_basisMonomials ℕ _) d
    rw [hb, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.neg_apply,
      lowerCoeffShift_monomial, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul,
      lowerCoeff_monomial]
    have h1 : (Finsupp.single j 1 + d : ℕ →₀ ℕ) j = d j + 1 := by
      rw [Finsupp.add_apply, Finsupp.single_eq_same]; ring
    have h2 : Finsupp.erase j (Finsupp.single j 1 + d) = Finsupp.erase j d := by
      rw [Finsupp.erase_add, Finsupp.erase_single, zero_add]
    rw [h1, h2, pow_succ]
    ring
  exact LinearMap.congr_fun h G

/-! ### `d_-` against the auxiliary variables -/

/-- `d_-^{(k)}(y_kF) = -d_-^{CM,(k)}F`: Carlsson--Mellit's lowering operator is `-d_-y_k`. -/
theorem dminus_auxVar_mul (q : L) (k : ℕ) (F : Total L) :
    dminus q (k + 1) (auxVar (k + 1) * F) = -dminusCM q (k + 1) F := by
  have hy : (auxVar (k + 1) : Total L) = X k := by rw [auxVar, Nat.add_sub_cancel]
  rw [dminus_apply, map_mul, hy, qshiftNeg_auxVar, Nat.add_sub_cancel, lowerCoeff_X_mul]
  rfl

/-! ### The operator `M` -/

/-- **`M_k = (-1)^k y_1⋯y_k`**, as an element of the total space. -/
noncomputable def mPoly {L : Type*} [Field L] : ℕ → Total L
  | 0 => 1
  | k + 1 => -(mPoly k * auxVar (k + 1))

omit [Algebra ℚ L] in
/-- `M_0 = 1`. -/
theorem mPoly_zero : (mPoly 0 : Total L) = 1 := rfl

omit [Algebra ℚ L] in
/-- `M_{k+1} = -(M_k y_{k+1})`. -/
theorem mPoly_succ (k : ℕ) : (mPoly (k + 1) : Total L) = -(mPoly k * auxVar (k + 1)) := rfl

/-- `d_-^{(k)}` commutes with `M_m` for `m < k`. -/
theorem dminus_mPoly_mul_of_lt (q : L) {m k : ℕ} (hmk : m < k) (F : Total L) :
    dminus q k (mPoly m * F) = mPoly m * dminus q k F := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  induction m generalizing F with
  | zero => rw [mPoly_zero, one_mul, one_mul]
  | succ m ih =>
    have e1 : ∀ G : Total L, -(mPoly m * auxVar (m + 1)) * G = -(mPoly m * (auxVar (m + 1) * G)) :=
      fun G => by ring
    rw [mPoly_succ, e1, e1, map_neg, ih _ (by omega),
      HJO.Sweep.dminus_auxVar_mul q (by omega) (by omega)]

/-- **`d_- ∘ M_k = M_{k-1} ∘ d_-^{CM}`** on `V_k`, read on the whole total space. -/
theorem dminus_mPoly_mul (q : L) (k : ℕ) (F : Total L) :
    dminus q (k + 1) (mPoly (k + 1) * F) = mPoly k * dminusCM q (k + 1) F := by
  have e1 : -(mPoly k * auxVar (k + 1)) * F = -(mPoly k * (auxVar (k + 1) * F)) := by ring
  rw [mPoly_succ, e1, map_neg, dminus_mPoly_mul_of_lt q (by omega), dminus_auxVar_mul]
  ring

/-- Carlsson--Mellit's `d_-^{CM,ℓ} = d_-^{CM,(1)} ∘ ⋯ ∘ d_-^{CM,(ℓ)}`, the mirror of
`HJO.Mellit.lowerRun`. -/
noncomputable def lowerRunCM (q : L) : ℕ → Module.End L (Total L)
  | 0 => 1
  | n + 1 => lowerRunCM q n * dminusCM q (n + 1)

/-- **`d_-^ℓ ∘ M_ℓ = d_-^{CM,ℓ}`**, `M_0` being the identity. -/
theorem lowerRun_mPoly_mul (q : L) (n : ℕ) (F : Total L) :
    lowerRun q n (mPoly n * F) = lowerRunCM q n F := by
  induction n generalizing F with
  | zero => rw [mPoly_zero, one_mul]; rfl
  | succ n ih =>
    change lowerRun q n (dminus q (n + 1) (mPoly (n + 1) * F))
      = lowerRunCM q n (dminusCM q (n + 1) F)
    rw [dminus_mPoly_mul, ih]

/-! ### `M` against `d^*_+` and the braid operators -/

omit [Algebra ℚ L] in
/-- `M_m` is fixed by `qshift q i`. -/
theorem qshift_mPoly (q : L) (i m : ℕ) : qshift q i (mPoly m : Total L) = mPoly m := by
  induction m with
  | zero => rw [mPoly_zero, map_one]
  | succ m ih => rw [mPoly_succ, map_neg, map_mul, ih, auxVar, qshift_auxVar]

omit [Algebra ℚ L] in
/-- `y_1 · cycleShift u k (M_m) = -M_{m+1}` for `m ≤ k`. -/
theorem auxVar_one_mul_cycleShift_mPoly (u : L) {k m : ℕ} (hm : m ≤ k) :
    (auxVar 1 : Total L) * cycleShift u k (mPoly m) = -mPoly (m + 1) := by
  induction m with
  | zero => rw [mPoly_zero, map_one, mPoly_succ, mPoly_zero]; ring
  | succ m ih =>
    rw [mPoly_succ, map_neg, map_mul, cycleShift_auxVar u (by omega) hm, mPoly_succ (m + 1)]
    linear_combination (-auxVar (m + 1 + 1) : Total L) * ih (by omega)

omit [Algebra ℚ L] in
/-- **`-y_1d^*_+ ∘ M_k = M_{k+1} ∘ d^*_+`.** -/
theorem neg_auxVar_one_mul_dplusStar_mPoly_mul (q u : L) (k : ℕ) (F : Total L) :
    -((auxVar 1 : Total L) * dplusStar q u k (mPoly k * F))
      = mPoly (k + 1) * dplusStar q u k F := by
  rw [dplusStar_apply, dplusStar_apply, map_mul, qshift_mPoly, map_mul, ← mul_assoc,
    auxVar_one_mul_cycleShift_mPoly u le_rfl]
  ring

omit [Algebra ℚ L] in
/-- `M_m` is symmetric in `y_i, y_{i+1}` for `m < i`. -/
theorem swapAux_mPoly_of_lt {i m : ℕ} (hmi : m + 1 ≤ i) :
    swapAux L i (mPoly m : Total L) = mPoly m := by
  induction m with
  | zero => rw [mPoly_zero, map_one]
  | succ m ih =>
    rw [mPoly_succ, map_neg, map_mul, ih (by omega), auxVar, Nat.add_sub_cancel, swapAux_X,
      Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]

omit [Algebra ℚ L] in
/-- `M_m` is symmetric in `y_i, y_{i+1}` for `1 ≤ i < m`. -/
theorem swapAux_mPoly {i m : ℕ} (hi : 1 ≤ i) (him : i + 1 ≤ m) :
    swapAux L i (mPoly m : Total L) = mPoly m := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge (i + 1) (m + 1) with h | h
    · rw [mPoly_succ, map_neg, map_mul, ih (by omega), auxVar, Nat.add_sub_cancel, swapAux_X,
        Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
    · have hm : i = m := by omega
      subst hm
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hv : swapAux L (j + 1) (auxVar (j + 1 + 1)) = (auxVar (j + 1) : Total L) := by
        rw [auxVar, auxVar, swapAux_X, Nat.add_sub_cancel, Nat.add_sub_cancel,
          Equiv.swap_apply_right]
      rw [mPoly_succ, mPoly_succ, map_neg, map_mul, map_neg, map_mul, swapAux_auxVar_self hi,
        swapAux_mPoly_of_lt (by omega), hv]
      ring

omit [Algebra ℚ L] in
/-- Multiplication by `M_m` commutes with the braid operator `T_i` for `1 ≤ i < m`. -/
theorem commute_mPoly_braidEnd (q : L) {i m : ℕ} (hi : 1 ≤ i) (him : i + 1 ≤ m) :
    Commute (LinearMap.mulLeft L (mPoly m : Total L)) (braidEnd q i) := by
  refine LinearMap.ext fun F => ?_
  change mPoly m * braid q i F = braid q i (mPoly m * F)
  rw [braid_symmetric_mul q (swapAux_mPoly hi him)]

omit [Algebra ℚ L] in
/-- Multiplication by `M_m` commutes with the inverse braid operator `T_i^{-1}` for
`1 ≤ i < m`. -/
theorem commute_mPoly_braidInvEnd (q : L) {i m : ℕ} (hi : 1 ≤ i) (him : i + 1 ≤ m) :
    Commute (LinearMap.mulLeft L (mPoly m : Total L)) (braidInvEnd q i) := by
  refine LinearMap.ext fun F => ?_
  change mPoly m * braidInv q i F = braidInv q i (mPoly m * F)
  rw [braidInv_apply, braidInv_apply, braid_symmetric_mul q (swapAux_mPoly hi him)]
  ring

omit [Algebra ℚ L] in
/-- A word in the braid operators of indices in `[1, m)` commutes with anything that commutes
with each of them. -/
theorem commute_list_prod {X : Module.End L (Total L)} (T : ℕ → Module.End L (Total L))
    {m : ℕ} (hT : ∀ j, 1 ≤ j → j + 1 ≤ m → Commute X (T j)) (l : List ℕ)
    (hl : ∀ j ∈ l, 1 ≤ j ∧ j + 1 ≤ m) : Commute X (l.map T).prod := by
  refine Commute.list_prod_right _ _ fun b hb => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
  exact hT j (hl j hj).1 (hl j hj).2

omit [Algebra ℚ L] in
/-- Multiplication by `M_m` commutes with `trainUpEnd q a b` for `1 ≤ a, b ≤ m`. -/
theorem commute_mPoly_trainUpEnd (q : L) {a b m : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (ham : a ≤ m)
    (hbm : b ≤ m) : Commute (LinearMap.mulLeft L (mPoly m : Total L)) (trainUpEnd q a b) := by
  rw [trainUpEnd, Braid.trainUp]
  split_ifs with h
  · exact commute_list_prod _ (fun j hj hjm => commute_mPoly_braidEnd q hj hjm) _
      fun j hj => by rw [List.mem_range'_1] at hj; omega
  · exact commute_list_prod _ (fun j hj hjm => commute_mPoly_braidInvEnd q hj hjm) _
      fun j hj => by rw [List.mem_reverse, List.mem_range'_1] at hj; omega

omit [Algebra ℚ L] in
/-- Multiplication by `M_m` commutes with `trainDownEnd q a b` for `1 ≤ a, b ≤ m`. -/
theorem commute_mPoly_trainDownEnd (q : L) {a b m : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (ham : a ≤ m)
    (hbm : b ≤ m) : Commute (LinearMap.mulLeft L (mPoly m : Total L)) (trainDownEnd q a b) := by
  rw [trainDownEnd, Braid.trainDown]
  split_ifs with h
  · exact commute_list_prod _ (fun j hj hjm => commute_mPoly_braidEnd q hj hjm) _
      fun j hj => by rw [List.mem_reverse, List.mem_range'_1] at hj; omega
  · exact commute_list_prod _ (fun j hj hjm => commute_mPoly_braidInvEnd q hj hjm) _
      fun j hj => by rw [List.mem_range'_1] at hj; omega

omit [Algebra ℚ L] in
/-- `trainUpEnd q a b (M_m F) = M_m · trainUpEnd q a b F` for `1 ≤ a, b ≤ m`. -/
theorem trainUpEnd_mPoly_mul (q : L) {a b m : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (ham : a ≤ m)
    (hbm : b ≤ m) (F : Total L) :
    trainUpEnd q a b (mPoly m * F) = mPoly m * trainUpEnd q a b F :=
  (LinearMap.congr_fun (commute_mPoly_trainUpEnd q ha hb ham hbm) F).symm

omit [Algebra ℚ L] in
/-- `trainDownEnd q a b (M_m F) = M_m · trainDownEnd q a b F` for `1 ≤ a, b ≤ m`. -/
theorem trainDownEnd_mPoly_mul (q : L) {a b m : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (ham : a ≤ m)
    (hbm : b ≤ m) (F : Total L) :
    trainDownEnd q a b (mPoly m * F) = mPoly m * trainDownEnd q a b F :=
  (LinearMap.congr_fun (commute_mPoly_trainDownEnd q ha hb ham hbm) F).symm

/-! ### The conjugated stage -/

/-- The first stage letter at `(1,1)`, conjugated by `M`: `T_{k+1↘1}d^*_+`. -/
noncomputable def oldOne (q u : L) (k : ℕ) : Module.End L (Total L) :=
  trainDownEnd q (k + 1) 1 * dplusStar q u k

/-- The replicated letter at `(1,1)`, conjugated by `M`:
`q/(1-q)·T_{k+1↘1}(d^*_+d_-^{CM} - d_-^{CM}d^*_+)` on `V_{k+1}`. -/
noncomputable def oldRep (q u : L) (k : ℕ) : Module.End L (Total L) :=
  (q / (1 - q)) • (trainDownEnd q (k + 1) 1 *
    (dplusStar q u k * dminusCM q (k + 1) - dminusCM q (k + 2) * dplusStar q u (k + 1)))

/-- The stage `G_{k+1,A}` at `(1,1)`, conjugated by `M`. -/
noncomputable def oldStage (q u : L) (k A : ℕ) : Module.End L (Total L) :=
  oldRep q u k ^ (A - 1) * oldOne q u k

/-- The stage word at `(1,1)`, conjugated by `M`, from the grading `k`. -/
noncomputable def oldStageFrom (q u : L) : ℕ → Total L → List ℕ → Total L
  | _, F, [] => F
  | k, F, A :: α => oldStageFrom q u (k + 1) (oldStage q u k A F) α

/-- At the slope `(1,1)`, the first stage letter is `-y_1d^*_+`. -/
theorem replOneTotal_one_one (q u : L) (k : ℕ) :
    replOneTotal q u 1 1 k = -(LinearMap.mulLeft L (auxVar 1 : Total L) * dplusStar q u k) := by
  rw [replOneTotal, slopeOperator_one_one]; simp

/-- At the slope `(1,1)`, the second stage letter is `-y_1` times `zopOneStar q u (k + 1)`. -/
theorem replTwoTotal_one_one (q u : L) (k : ℕ) :
    replTwoTotal q u 1 1 k
      = -(LinearMap.mulLeft L (auxVar 1 : Total L) * zopOneStar q u (k + 1)) := by
  rw [replTwoTotal, slopeOperator_one_one]; simp

/-- **The first letter**: `T_{k+1↘1}(-y_1d^*_+) ∘ M_k = M_{k+1} ∘ T_{k+1↘1}d^*_+`. -/
theorem trainDown_replOne_mPoly_mul (q u : L) (k : ℕ) (F : Total L) :
    trainDownEnd q (k + 1) 1 (replOneTotal q u 1 1 k (mPoly k * F))
      = mPoly (k + 1) * oldOne q u k F := by
  rw [replOneTotal_one_one, LinearMap.neg_apply, Module.End.mul_apply, LinearMap.mulLeft_apply,
    neg_auxVar_one_mul_dplusStar_mPoly_mul, trainDownEnd_mPoly_mul q (by omega) le_rfl le_rfl
      (by omega)]
  rfl

/-- **`-y_1z_1 ∘ M_{k+1} = M_{k+1} ∘ q^{k+1}/(1-q)(d^*_+d_-^{CM} - d_-^{CM}d^*_+)T^*_{k+1↘1}`.** -/
theorem replTwo_mPoly_mul (q u : L) (k : ℕ) (G : Total L) :
    replTwoTotal q u 1 1 k (mPoly (k + 1) * G)
      = mPoly (k + 1) * ((q ^ (k + 1) / (1 - q)) •
        (dplusStar q u k (dminusCM q (k + 1) (trainUpEnd q (k + 1) 1 G))
          - dminusCM q (k + 2) (dplusStar q u (k + 1) (trainUpEnd q (k + 1) 1 G)))) := by
  set H := trainUpEnd q (k + 1) 1 G with hH
  have hT : trainUpEnd q (k + 1) 1 (mPoly (k + 1) * G) = mPoly (k + 1) * H :=
    trainUpEnd_mPoly_mul q (by omega) le_rfl le_rfl (by omega) G
  have h1 : (auxVar 1 : Total L) * dplusStar q u k (dminus q (k + 1) (mPoly (k + 1) * H))
      = -(mPoly (k + 1) * dplusStar q u k (dminusCM q (k + 1) H)) := by
    rw [dminus_mPoly_mul, ← neg_auxVar_one_mul_dplusStar_mPoly_mul, neg_neg]
  have h2 : (auxVar 1 : Total L) * dminus q (k + 2) (dplusStar q u (k + 1) (mPoly (k + 1) * H))
      = -(mPoly (k + 1) * dminusCM q (k + 2) (dplusStar q u (k + 1) H)) := by
    rw [← HJO.Sweep.dminus_auxVar_mul q (k := k + 1) le_rfl (by omega),
      show (auxVar 1 : Total L) * dplusStar q u (k + 1) (mPoly (k + 1) * H)
        = -(mPoly (k + 2) * dplusStar q u (k + 1) H) by
          rw [← neg_auxVar_one_mul_dplusStar_mPoly_mul, neg_neg],
      map_neg, dminus_mPoly_mul]
  rw [replTwoTotal_one_one, LinearMap.neg_apply, Module.End.mul_apply, LinearMap.mulLeft_apply,
    zopOneStar, LinearMap.smul_apply, Module.End.mul_apply, hT, LinearMap.sub_apply,
    Module.End.mul_apply, Module.End.mul_apply, Nat.add_sub_cancel, mul_smul_comm, mul_sub, h1,
    h2, smul_sub, mul_smul_comm, mul_sub]
  simp only [smul_neg, smul_sub]
  abel

omit [Algebra ℚ L] in
/-- For `q ≠ 0`, `trainUpEnd q (k + 1) 1` is a left inverse of `trainUpEnd q 1 (k + 1)`. -/
theorem trainUpEnd_down_up (q : L) (hq : q ≠ 0) (k : ℕ) (G : Total L) :
    trainUpEnd q (k + 1) 1 (trainUpEnd q 1 (k + 1) G) = G := by
  have h := Braid.trainUp_mul_trainUp_self (isBraidSystem_braidEnd q hq (k + 1))
    (a := k + 1) (b := 1) (by omega) le_rfl le_rfl (by omega)
  exact LinearMap.congr_fun h G

/-- **The replicated letter**: `Z^{(k+1)}_{1,1} ∘ M_{k+1} = M_{k+1} ∘ oldRep`. -/
theorem replicated_mPoly_mul (q u : L) (hq : q ≠ 0) (k : ℕ) (G : Total L) :
    replicatedTotal q u 1 1 k (mPoly (k + 1) * G) = mPoly (k + 1) * oldRep q u k G := by
  have hscal : (q : L) ^ (-(k : ℤ)) * (q ^ (k + 1) / (1 - q)) = q / (1 - q) := by
    rw [zpow_neg, zpow_natCast, pow_succ]
    field_simp
  rw [replicatedTotal, LinearMap.smul_apply, Module.End.mul_apply, Module.End.mul_apply,
    trainUpEnd_mPoly_mul q le_rfl (by omega) (by omega) le_rfl, replTwo_mPoly_mul,
    trainUpEnd_down_up q hq, trainDownEnd_mPoly_mul q (by omega) le_rfl le_rfl (by omega),
    map_smul, mul_smul_comm, smul_smul, hscal, oldRep, LinearMap.smul_apply, mul_smul_comm]
  rfl

/-- **The stage at `(1,1)`**: `G_{k+1,A} ∘ M_k = M_{k+1} ∘ oldStage`. -/
theorem stageTotal_one_one_mPoly_mul (q u : L) (hq : q ≠ 0) (k A : ℕ) (F : Total L) :
    stageTotal q u 1 1 k A (mPoly k * F) = mPoly (k + 1) * oldStage q u k A F := by
  rw [stageTotal, oldStage, Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply,
    trainDown_replOne_mPoly_mul]
  generalize oldOne q u k F = G
  induction A - 1 generalizing G with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply,
      replicated_mPoly_mul q u hq, ih]

/-- **The stage word at `(1,1)`**, conjugated by `M`, from any grading. -/
theorem stageFromTotal_one_one_mPoly_mul (q u : L) (hq : q ≠ 0) (α : List ℕ) :
    ∀ (k : ℕ) (F : Total L), stageFromTotal q u 1 1 k (mPoly k * F) α
      = mPoly (k + α.length) * oldStageFrom q u k F α := by
  induction α with
  | nil => intro k F; rfl
  | cons A α ih =>
    intro k F
    rw [stageFromTotal, oldStageFrom, stageTotal_one_one_mPoly_mul q u hq, ih,
      List.length_cons, Nat.add_assoc, Nat.add_comm 1]

/-- **The right-hand side of the clause at `(1,1)`, in Carlsson--Mellit's operators**:
`ct(d_-^ℓG_ℓ⋯G_1(1)) = ct(d_-^{CM,ℓ}(oldStageFrom 0 1 α))`. -/
theorem lhsOp_one_one_apply_one_eq_lowerRunCM (q u : L) (hq : q ≠ 0) (α : List ℕ) :
    lhsOp q u 1 1 α 1
      = constantCoeff (lowerRunCM q α.length (oldStageFrom q u 0 1 α)) := by
  rw [lhsOp_apply_one, stageWordTotal, ← mul_one (1 : Total L),
    show (1 : Total L) * 1 = mPoly 0 * 1 from by rw [mPoly_zero],
    stageFromTotal_one_one_mPoly_mul q u hq, Nat.zero_add, lowerRun_mPoly_mul, mPoly_zero,
    one_mul]

end HJO.Mellit.LhsDesign
