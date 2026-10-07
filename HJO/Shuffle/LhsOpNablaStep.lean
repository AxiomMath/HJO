/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.LhsOpIntertwiner
public import HJO.Shuffle.LhsOpDefs

/-! # The `N`-step of the operator clause on the sweep side

For the normalised Macdonald conjugator `∇` and coprime `m, n ≥ 1`, the right-hand side of the
operator clause of `HJO.Mellit.lhsRewrite_sweepWitness` satisfies

`lhsOp_{m+n,n}(α) ∘ ∇ = (-1)^{n|α|} ∇ ∘ lhsOp_{m,n}(α)`,

the sweep half of Mellit's step `N : (m,n) ↦ (m+n,n)` (§3.7, `∇'L = N(L)∇'`). Mellit's
`∇'`, read on every graded piece (`HJO.Sweep.IsNablaPrime`), shears the slope operator,
`𝒩Ξ_{m,n}(-y_1F) = Ξ_{m+n,n}(-y_1𝒩F)`, and commutes with `d_-`, `d_+^*`, `z_1` and the trains. So
it carries each replication letter `Ω(1;m,n)`, `Ω(2;m,n)`, `Z_{m,n}` to `(-1)^n` times the same
letter at `(m+n,n)`, the sign coming from the prefactor `(-1)^{a-1}`; a stage `G_{k+1,A}` to
`(-1)^{nA}` times its shear; the stage word to `(-1)^{n|α|}` times its shear; and it commutes with
the lowering run `d_-^ℓ`. On `V_0` it is `∇`.

## Main results

* `HJO.Sweep.IsNablaPrime.map_replOneTotal`, `HJO.Sweep.IsNablaPrime.map_replTwoTotal`,
  `HJO.Sweep.IsNablaPrime.map_replicatedTotal`, `HJO.Sweep.IsNablaPrime.map_stageTotal`: the
  letters of the stage word along `N`.
* `HJO.Sweep.IsNablaPrime.map_stageFromEnd`, `HJO.Sweep.IsNablaPrime.map_lowerRun`: the stage word
  and the lowering run.
* `HJO.Mellit.LhsDesign.lhsOp_add_left`: the `N`-step of the operator clause.

## References

* [A. Mellit, *Toric braids and (m,n)-parking functions*][mellit2016], §3.7.
-/

@[expose] public section

namespace HJO.Sweep

open MvPolynomial HJO.Mellit HJO.Mellit.LhsDesign

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {nabla : Module.End L (Sym.Lambda L)}
  {N : ℕ → Module.End L (Total L)}

omit [Algebra ℚ L] in
/-- The sign of the slope prefactor along `N`: `(-1)^n(-1)^{m+n-1} = (-1)^{m-1}`. -/
theorem neg_one_pow_mul_neg_one_pow_add {m n : ℕ} (hm : 1 ≤ m) :
    (-1 : L) ^ n * (-1 : L) ^ (m + n - 1) = (-1 : L) ^ (m - 1) := by
  rw [← pow_add, show n + (m + n - 1) = (m - 1) + 2 * n from by omega, pow_add, pow_mul,
    neg_one_sq, one_pow, mul_one]

namespace IsNablaPrime

variable (hN : IsNablaPrime q u nabla N)
include hN

/-- **`Ω(1;m,n)` along `N`**: `𝒩_{k+1}Ω(1;m,n) = (-1)^nΩ(1;m+n,n)𝒩_k` out of `V_k`. -/
theorem map_replOneTotal (hq : q ≠ 0) {m n : ℕ} (hmn : Nat.Coprime m n) (hm : 1 ≤ m)
    (hn : 1 ≤ n) (k : ℕ) {F : Total L} (hF : F ∈ piece L k) :
    N (k + 1) (replOneTotal q u m n k F)
      = ((-1 : L) ^ n) • replOneTotal q u (m + n) n k (N k F) := by
  simp only [replOneTotal, LinearMap.smul_apply, Module.End.mul_apply, LinearMap.neg_apply,
    LinearMap.mulLeft_apply]
  rw [map_smul, hN.map_slopeOperator_neg_auxVar_mul hq (by omega) hmn hm hn
    (dplusStar_mem_piece q u hF), hN.map_dplusStar k hF, smul_smul,
    neg_one_pow_mul_neg_one_pow_add (L := L) hm]

/-- **`Ω(2;m,n)` along `N`**: `𝒩_{k+1}Ω(2;m,n) = (-1)^nΩ(2;m+n,n)𝒩_{k+1}` on `V_{k+1}`. -/
theorem map_replTwoTotal (hq : q ≠ 0) {m n : ℕ} (hmn : Nat.Coprime m n) (hm : 1 ≤ m)
    (hn : 1 ≤ n) (k : ℕ) {F : Total L} (hF : F ∈ piece L (k + 1)) :
    N (k + 1) (replTwoTotal q u m n k F)
      = ((-1 : L) ^ n) • replTwoTotal q u (m + n) n k (N (k + 1) F) := by
  simp only [replTwoTotal, LinearMap.smul_apply, Module.End.mul_apply, LinearMap.neg_apply,
    LinearMap.mulLeft_apply]
  rw [map_smul, hN.map_slopeOperator_neg_auxVar_mul hq (by omega) hmn hm hn
    (zopOneStar_mem_piece q u (by omega) hF), hN.map_zopOneStar hq (by omega) hF, smul_smul,
    neg_one_pow_mul_neg_one_pow_add (L := L) hm]

/-- **`Z_{m,n}` along `N`**: `𝒩_{k+1}Z^{(k+1)}_{m,n} = (-1)^nZ^{(k+1)}_{m+n,n}𝒩_{k+1}`. -/
theorem map_replicatedTotal (hq : q ≠ 0) {m n : ℕ} (hmn : Nat.Coprime m n) (hm : 1 ≤ m)
    (hn : 1 ≤ n) (k : ℕ) {F : Total L} (hF : F ∈ piece L (k + 1)) :
    N (k + 1) (replicatedTotal q u m n k F)
      = ((-1 : L) ^ n) • replicatedTotal q u (m + n) n k (N (k + 1) F) := by
  have h1 : trainUpEnd q 1 (k + 1) F ∈ piece L (k + 1) :=
    trainUpEnd_mem_piece q (by omega) le_rfl hF
  have h2 : replTwoTotal q u m n k (trainUpEnd q 1 (k + 1) F) ∈ piece L (k + 1) :=
    replTwoTotal_mem_piece q u m n k h1
  simp only [replicatedTotal, LinearMap.smul_apply, Module.End.mul_apply]
  rw [map_smul, hN.map_trainDownEnd hq (by omega) le_rfl le_rfl (by omega) h2,
    hN.map_replTwoTotal hq hmn hm hn k h1, map_smul,
    hN.map_trainUpEnd hq le_rfl (by omega) (by omega) le_rfl hF, smul_comm]

theorem map_replicatedTotal_pow (hq : q ≠ 0) {m n : ℕ} (hmn : Nat.Coprime m n) (hm : 1 ≤ m)
    (hn : 1 ≤ n) (k : ℕ) :
    ∀ (j : ℕ) {F : Total L}, F ∈ piece L (k + 1) →
      N (k + 1) ((replicatedTotal q u m n k ^ j) F)
        = ((-1 : L) ^ (n * j)) • (replicatedTotal q u (m + n) n k ^ j) (N (k + 1) F) := by
  intro j
  induction j with
  | zero => intro F _; simp
  | succ j ih =>
    intro F hF
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply,
      ih (replicatedTotal_mem_piece q u m n k hF), hN.map_replicatedTotal hq hmn hm hn k hF,
      map_smul, smul_smul, ← pow_add, show n * j + n = n * (j + 1) from by ring]

/-- **A stage along `N`**: `𝒩_{k+1}G^{m,n}_{k+1,A} = (-1)^{nA}G^{m+n,n}_{k+1,A}𝒩_k` out of `V_k`,
for `A ≥ 1`. -/
theorem map_stageTotal (hq : q ≠ 0) {m n : ℕ} (hmn : Nat.Coprime m n) (hm : 1 ≤ m)
    (hn : 1 ≤ n) (k : ℕ) {A : ℕ} (hA : 1 ≤ A) {F : Total L} (hF : F ∈ piece L k) :
    N (k + 1) (stageTotal q u m n k A F)
      = ((-1 : L) ^ (n * A)) • stageTotal q u (m + n) n k A (N k F) := by
  have h1 : replOneTotal q u m n k F ∈ piece L (k + 1) := replOneTotal_mem_piece q u m n k hF
  have h2 : trainDownEnd q (k + 1) 1 (replOneTotal q u m n k F) ∈ piece L (k + 1) :=
    trainDownEnd_mem_piece q le_rfl (by omega) h1
  simp only [stageTotal, Module.End.mul_apply]
  rw [hN.map_replicatedTotal_pow hq hmn hm hn k (A - 1) h2,
    hN.map_trainDownEnd hq (by omega) le_rfl le_rfl (by omega) h1,
    hN.map_replOneTotal hq hmn hm hn k hF, map_smul, map_smul, smul_smul, ← pow_add,
    show n * (A - 1) + n = n * A from by
      obtain ⟨B, rfl⟩ : ∃ B, A = B + 1 := ⟨A - 1, by omega⟩
      rw [Nat.add_sub_cancel]; ring]

/-- **The stage word along `N`**:
`𝒩_{k+ℓ}G^{m,n}_ℓ⋯G^{m,n}_{k+1} = (-1)^{n|α|}G^{m+n,n}_ℓ⋯G^{m+n,n}_{k+1}𝒩_k` out of `V_k`, for a
composition `α` with positive parts. -/
theorem map_stageFromEnd (hq : q ≠ 0) {m n : ℕ} (hmn : Nat.Coprime m n) (hm : 1 ≤ m)
    (hn : 1 ≤ n) :
    ∀ (α : List ℕ), (∀ x ∈ α, 0 < x) → ∀ (k : ℕ) {F : Total L}, F ∈ piece L k →
      N (k + α.length) (stageFromEnd q u m n k α F)
        = ((-1 : L) ^ (n * α.sum)) • stageFromEnd q u (m + n) n k α (N k F) := by
  intro α
  induction α with
  | nil => intro _ k F _; simp [stageFromEnd]
  | cons A α ih =>
    intro hpos k F hF
    have hA : 1 ≤ A := hpos A List.mem_cons_self
    have hS : stageTotal q u m n k A F ∈ piece L (k + 1) := stageTotal_mem_piece q u m n k A hF
    simp only [stageFromEnd, Module.End.mul_apply]
    rw [List.length_cons, show k + (α.length + 1) = k + 1 + α.length from by omega,
      ih (fun x hx => hpos x (List.mem_cons_of_mem _ hx)) (k + 1) hS,
      hN.map_stageTotal hq hmn hm hn k hA hF, map_smul, smul_smul, ← pow_add, List.sum_cons,
      mul_add, add_comm (n * α.sum)]

/-- **The lowering run along `N`**: `𝒩_0 d_-^ℓ = d_-^ℓ 𝒩_ℓ` out of `V_ℓ`. -/
theorem map_lowerRun : ∀ (l : ℕ) {G : Total L}, G ∈ piece L l →
    N 0 (lowerRun q l G) = lowerRun q l (N l G) := by
  intro l
  induction l with
  | zero => intro G _; rfl
  | succ l ih =>
    intro G hG
    have hD : dminus q (l + 1) G ∈ piece L l := by simpa using dminus_mem_piece q (l + 1) hG
    rw [lowerRun, Module.End.mul_apply, Module.End.mul_apply, ih hD, hN.map_dminus l hG]

end IsNablaPrime

end HJO.Sweep

namespace HJO.Mellit.LhsDesign

open HJO.Sym HJO.Sweep HJO.Ascent MvPolynomial

variable (K : Type*) [Field K] [Algebra ParamRing K] [IsFractionRing ParamRing K] [Algebra ℚ K]

local notation "𝗊" => paramQ K
local notation "𝗎" => paramU K

/-- **The `N`-step of the operator clause on the sweep side, at every grading.** For the
normalised Macdonald conjugator, `lhsOp (m+n) n α ∘ ∇ = (-1)^{n|α|} ∇ ∘ lhsOp m n α`.

Mellit's `∇'`, read on every piece (`HJO.Sweep.exists_isNablaPrime_param`), is `∇` on `V_0`,
carries the stage word at `(m,n)` to `(-1)^{n|α|}` times the stage word at `(m+n,n)`
(`HJO.Sweep.IsNablaPrime.map_stageFromEnd`) and commutes with the lowering run
(`HJO.Sweep.IsNablaPrime.map_lowerRun`). -/
theorem lhsOp_add_left {nabla : Module.End K (Sym.Lambda K)}
    (hnab : IsMacdonaldConjugator 𝗊 𝗎 nabla) (hone : nabla 1 = 1) {m n : ℕ}
    (hmn : Nat.Coprime m n) (hm : 1 ≤ m) (hn : 1 ≤ n) (α : List ℕ) (hpos : ∀ x ∈ α, 0 < x)
    (f : Sym.Lambda K) :
    lhsOp 𝗊 𝗎 (m + n) n α (nabla f)
      = ((-1 : K) ^ (n * α.sum)) • nabla (lhsOp 𝗊 𝗎 m n α f) := by
  obtain ⟨N, hN⟩ := exists_isNablaPrime_param K hnab hone
  have hq : (𝗊 : K) ≠ 0 := Invertible.ne_zero _
  set s : K := (-1 : K) ^ (n * α.sum) with hs
  have hss : s * s = 1 := by rw [hs, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hC : (C f : Total K) ∈ piece K 0 := C_mem_piece_zero f
  have hG : stageFromEnd 𝗊 𝗎 m n 0 α (C f) ∈ piece K α.length := by
    simpa using stageFromEnd_mem_piece 𝗊 𝗎 m n α 0 hC
  obtain ⟨h, hh⟩ := exists_C_eq_of_mem_piece_zero
    (lowerRun_mem_piece_zero 𝗊 α.length hG)
  have hS := hN.map_stageFromEnd hq hmn hm hn α hpos 0 hC
  rw [zero_add] at hS
  have hS' : stageFromEnd 𝗊 𝗎 (m + n) n 0 α (N 0 (C f))
      = s • N α.length (stageFromEnd 𝗊 𝗎 m n 0 α (C f)) := by
    rw [hS, smul_smul, hss, one_smul]
  have hlhs : lhsOp 𝗊 𝗎 m n α f = h := by
    change constantCoeff ((lowerRun 𝗊 α.length * stageFromEnd 𝗊 𝗎 m n 0 α) (C f)) = h
    rw [Module.End.mul_apply, ← hh, constantCoeff_C]
  change constantCoeff ((lowerRun 𝗊 α.length * stageFromEnd 𝗊 𝗎 (m + n) n 0 α)
    (C (nabla f))) = _
  rw [Module.End.mul_apply, ← hN.map_C, hS', map_smul, ← hN.map_lowerRun α.length hG, ← hh,
    hN.map_C, hlhs]
  change constantCoeffLin (s • constLin (nabla h)) = _
  rw [map_smul]
  change s • constantCoeff (C (nabla h) : Total K) = _
  rw [constantCoeff_C]

end HJO.Mellit.LhsDesign
