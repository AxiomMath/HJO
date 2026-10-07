/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.LhsOpLambda
public import HJO.Shuffle.LhsOpNablaStep
public import HJO.Shuffle.LhsOpShiftStep
public import HJO.Shuffle.LhsOpBaseMul

/-! # The assembly of the operator clause by Euclid's algorithm

The operator clause `HJO.Mellit.LhsDesign.OpClause` is carried from the base slope `(1,1)` to every
positive coprime slope by Mellit's two moves, `N : (m,n) ↦ (m+n,n)` (`lhsOp_add_left`,
`theta_add_left`) and `S : (m,n) ↦ (m,n+m)` (`lhsOp_add_self`, `theta_add_self_nsTransports`). At
the base slope, `lhsOp_one_one_isMul` and `theta_one_one` reduce the clause to its value at the
vacuum, which is the hypothesis `hbase` here: Mellit's formula for `C_α` at the slope `(1,1)`.

## Main results

* `HJO.Mellit.LhsDesign.opClause_of_coprime_of_base`: the operator clause at every coprime slope.
* `HJO.Mellit.LhsDesign.lhsWord_standing_of_base`: `HJO.Mellit.lhsRewrite_sweepWitness` at `ℚ(q,u)`,
  from the base value alone.
-/

@[expose] public section

namespace HJO.Mellit.LhsDesign

open HJO.Sym HJO.Sweep HJO.Ascent MvPolynomial

variable (K : Type*) [Field K] [Algebra ParamRing K] [IsFractionRing ParamRing K] [Algebra ℚ K]

local notation "𝗊" => paramQ K
local notation "𝗎" => paramU K

/-! ### Assembly (proved from the leaves) -/

/-- The base `(1,1)` of the operator clause. -/
theorem opClause_one_one_of_base
    (hbase : ∀ {nabla : Module.End K (Sym.Lambda K)}, IsMacdonaldConjugator 𝗊 𝗎 nabla →
      nabla 1 = 1 → ∀ α : List ℕ, (∀ x ∈ α, 0 < x) →
      lhsOp 𝗊 𝗎 1 1 α 1 = (𝗊 ^ ((α.sum : ℤ) - (α.length : ℤ))) • nabla (CopComp 𝗊 α 1)) :
    OpClause 𝗊 𝗎 1 1 := by
  obtain ⟨nabla, hnab, hone⟩ := exists_nabla K
  intro Θ hΘ N hN α hpos hsum
  apply LinearMap.ext
  intro f
  obtain ⟨g, rfl⟩ := hnab.bijective.2 f
  obtain ⟨c, hc⟩ := lhsOp_one_one_isMul K hnab hone α hpos
  have hval := hbase hnab hone α hpos
  have h1 := hc 1
  rw [hone, mul_one] at h1
  rw [h1, ← map_smul] at hval
  have hcv : c = (𝗊 ^ ((α.sum : ℤ) - (α.length : ℤ))) • CopComp 𝗊 α 1 :=
    hnab.bijective.1 hval
  have hq := paramQ_ne_zero K
  rw [LinearMap.smul_apply, LinearMap.smul_apply, theta_one_one K hnab hΘ, hc, hcv,
    smul_mul_assoc, map_smul, smul_smul, ← hsum, show (1 - 1) * α.sum = 0 from by simp,
    pow_zero, one_mul, ← zpow_add₀ hq, show ((α.length : ℤ) - α.sum) + (α.sum - α.length) = 0
      from by ring, zpow_zero, one_smul, show α.sum * (1 + 1) = 2 * α.sum from by ring,
    pow_mul, neg_one_sq, one_pow, one_smul]

/-- The `N`-step of the operator clause. -/
theorem opClause_add_left {m n : ℕ} (hmn : Nat.Coprime m n) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (h : OpClause 𝗊 𝗎 m n) : OpClause 𝗊 𝗎 (m + n) n := by
  obtain ⟨nabla, hnab, hone⟩ := exists_nabla K
  obtain ⟨Θ, hΘ⟩ := exists_slopeHom K m n hmn hm hn
  intro Θ' hΘ' N hN α hpos hsum
  apply LinearMap.ext
  intro f
  obtain ⟨g, rfl⟩ := hnab.bijective.2 f
  have hc := LinearMap.congr_fun (h Θ hΘ N hN α hpos hsum) g
  rw [LinearMap.smul_apply, LinearMap.smul_apply] at hc
  rw [LinearMap.smul_apply, LinearMap.smul_apply, theta_add_left K hnab hm hn hΘ hΘ',
    lhsOp_add_left K hnab hone hmn hm hn α hpos, ← map_smul, hc, map_smul, smul_smul, hsum,
    show m + n - 1 = (m - 1) + n from by omega]
  congr 1
  have hb : (-1 : K) ^ (n * N) * (-1 : K) ^ (n * N) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [add_mul, pow_add]
  linear_combination (-((-1 : K) ^ ((m - 1) * N) * 𝗊 ^ ((α.length : ℤ) - (N : ℤ)))) * hb

/-- The `S`-step of the operator clause. -/
theorem opClause_add_self {m n : ℕ} (hmn : Nat.Coprime m n) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (h : OpClause 𝗊 𝗎 m n) : OpClause 𝗊 𝗎 m (n + m) := by
  obtain ⟨Θ, hΘ⟩ := exists_slopeHom K m n hmn hm hn
  intro Θ' hΘ' N hN α hpos hsum
  set s : K := (-1 : K) ^ ((m - 1) * N) * 𝗊 ^ ((α.length : ℤ) - (N : ℤ)) with hs
  have hs0 : s ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (zpow_ne_zero _ (paramQ_ne_zero K))
  have hg : CopComp 𝗊 α 1 ∈ LambdaComp K N := copComp_one_mem_lambdaComp 𝗊 hsum
  have hD : ShiftsDegree ((n : ℤ) * N) (Θ (CopComp 𝗊 α 1)) :=
    isSlopeHom_shiftsDegree' K hn hΘ hg
  have hlhs : lhsOp 𝗊 𝗎 m n α = (s⁻¹ * (-1 : K) ^ (N * (n + 1))) • Θ (CopComp 𝗊 α 1) := by
    rw [mul_smul, h Θ hΘ N hN α hpos hsum, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  have hrD : ShiftsDegree ((n : ℤ) * N)
      ((s⁻¹ * (-1 : K) ^ (N * (n + 1))) • Θ (CopComp 𝗊 α 1)) :=
    mem_degreeShifting.1 (Submodule.smul_mem _ _ (mem_degreeShifting.2 hD))
  have hD' : ShiftsDegree ((n : ℤ) * N) (lhsOp 𝗊 𝗎 m n α) := hlhs ▸ hrD
  have hT' : NsTransports 𝗊 𝗎 hD'
      ((s⁻¹ * (-1 : K) ^ (N * (n + 1))) • (((-1 : K) ^ (m * N)) • Θ' (CopComp 𝗊 α 1))) :=
    NsTransports.congr (hD := hrD) rfl hlhs.symm rfl
      (NsTransports.smul (hrD := hrD) _ (theta_add_self_nsTransports K hm hn hΘ hΘ' hg hD))
  rw [← nsShiftComp_eq_of_eq 𝗊 𝗎 hD' hT' (lhsOp_add_self K hmn hm hn α hpos hD'), smul_smul,
    smul_smul, ← mul_assoc, mul_comm s, mul_assoc, mul_assoc, inv_mul_cancel_left₀ hs0, ← pow_add,
    show N * (n + 1) + m * N = N * (n + m + 1) by ring]

/-- **Euclid's algorithm**: the operator clause at every positive coprime slope. -/
theorem opClause_of_coprime_of_base
    (hbase : ∀ {nabla : Module.End K (Sym.Lambda K)}, IsMacdonaldConjugator 𝗊 𝗎 nabla →
      nabla 1 = 1 → ∀ α : List ℕ, (∀ x ∈ α, 0 < x) →
      lhsOp 𝗊 𝗎 1 1 α 1 = (𝗊 ^ ((α.sum : ℤ) - (α.length : ℤ))) • nabla (CopComp 𝗊 α 1)) :
    ∀ a b : ℕ, Nat.Coprime a b → 1 ≤ a → 1 ≤ b → OpClause 𝗊 𝗎 a b := by
  intro a b
  induction h : a + b using Nat.strong_induction_on generalizing a b with
  | _ s ih =>
    intro hab ha hb
    rcases lt_trichotomy a b with hlt | heq | hgt
    · obtain ⟨c, rfl⟩ : ∃ c, b = c + a := ⟨b - a, by omega⟩
      have hac : Nat.Coprime a c := Nat.coprime_add_self_right.1 hab
      have hc : 1 ≤ c := by
        by_contra h0
        obtain rfl : c = 0 := by omega
        rw [zero_add, Nat.coprime_self] at hab
        omega
      exact opClause_add_self K hac ha hc (ih (a + c) (by omega) a c rfl hac ha hc)
    · subst heq
      rw [Nat.coprime_self] at hab
      subst hab
      exact opClause_one_one_of_base K hbase
    · obtain ⟨c, rfl⟩ : ∃ c, a = c + b := ⟨a - b, by omega⟩
      have hcb : Nat.Coprime c b := Nat.coprime_add_self_left.1 hab
      have hc : 1 ≤ c := by
        by_contra h0
        obtain rfl : c = 0 := by omega
        rw [zero_add, Nat.coprime_self] at hab
        omega
      exact opClause_add_left K hcb hc hb (ih (c + b) (by omega) c b rfl hcb hc hb)

/-- **`HJO.Mellit.lhsRewrite_sweepWitness` at the standing field**, in its `Λ`-level form. -/
theorem lhsWord_standing_of_base
    (hbase : ∀ {nabla : Module.End K (Sym.Lambda K)}, IsMacdonaldConjugator 𝗊 𝗎 nabla →
      nabla 1 = 1 → ∀ α : List ℕ, (∀ x ∈ α, 0 < x) →
      lhsOp 𝗊 𝗎 1 1 α 1 = (𝗊 ^ ((α.sum : ℤ) - (α.length : ℤ))) • nabla (CopComp 𝗊 α 1)) :
    ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b → LhsWord (paramQ K) (paramU K) a b :=
  fun a b hab ha hlt =>
    lhsWord_of_opClause (opClause_of_coprime_of_base K hbase a b hab ha.le (by omega))

end HJO.Mellit.LhsDesign
