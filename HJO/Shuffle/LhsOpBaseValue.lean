/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.LhsOpBaseValueN
public import HJO.CMStructure.StandingStructure

/-! # The base slope at the vacuum: Mellit's formula for `C_α`

**A step towards `HJO.Mellit.lhsRewrite_sweepWitness`**:
`ct(d_-^ℓG^{(1,1)}_ℓ⋯G^{(1,1)}_1(1)) = q^{N-ℓ}∇(C_α1)` at the standing field, for the Macdonald
conjugator normalised by `∇1 = 1` (`HJO.Mellit.LhsDesign.lhsOp_one_one_apply_one`).

A. Mellit (*Toric braids and `(m, n)`-parking functions*, arXiv:1604.07456, §3.7) asserts this
from E. Carlsson and A. Mellit (*A proof of the shuffle conjecture*, arXiv:1508.06239). The proof
here is Carlsson--Mellit's own proof of `∇C_α(1) = D_α`, read backwards:

1. `M = (-1)^ky_1⋯y_k` conjugates the `(1,1)` stage word into Carlsson--Mellit's original starred
   operators, and `d_-^ℓ` into `d_-^{CM,ℓ}`
   (`HJO.Mellit.LhsDesign.lhsOp_one_one_apply_one_eq_lowerRunCM`,
   `HJO/Shuffle/LhsOpBaseValueM.lean`);
2. the conjugation operator `𝒩` of `HJO.Sweep.exists_isConjugationOperator` carries the monomial
   `y_1^{α_1-1}⋯y_ℓ^{α_ℓ-1}` to that conjugated word, letter by letter
   (`HJO.Mellit.LhsDesign.NRel.unFrom`, `HJO/Shuffle/LhsOpBaseValueN.lean`), and commutes with
   `d_-^{CM}`;
3. `d_-^{CM,ℓ}(y_1^{α_1-1}⋯y_ℓ^{α_ℓ-1}) = (-1)^ℓB_α(1)` (`HJO.Sweep.dminusCM_auxVar_pow_mul`), and
   `ω̄B_α(1) = (-q)^{N-ℓ}C_α(1)` (`HJO.Sym.cop_omegaBar`);
4. on `V_0`, `𝒩 = ε_±∇ω̄` (`HJO.Sweep.conjugation_eq_signGrading_conjugator_omegaBar`), `∇`
   preserving degree (`HJO.Sym.IsMacdonaldConjugator.mem_lambdaComp`).

The signs `(-1)^ℓ`, `(-1)^{N-ℓ}` and `ε_± = (-1)^N` cancel, leaving `q^{N-ℓ}`.
-/

@[expose] public section

namespace HJO.Mellit.LhsDesign

open HJO.Sym HJO.Sweep HJO.Ascent MvPolynomial

/-! ### The standing field -/

variable (K : Type*) [Field K] [Algebra ParamRing K] [IsFractionRing ParamRing K] [Algebra ℚ K]

local notation "𝗊" => paramQ K
local notation "𝗎" => paramU K

/-- **The base slope at the vacuum: Mellit's formula for `C_α`.**
`ct(d_-^ℓ G^{(1,1)}_ℓ ⋯ G^{(1,1)}_1(1)) = q^{N-ℓ} ∇(C_α 1)`; equivalently `LhsWord 𝗊 𝗎 1 1`
(the compositional shuffle's algebraic side).

Mellit, §3.7, states `C_α = (-1)^kq^{r-k}ρ^*_{0,1}(d_-^r y^{α-1} d_+^r)1` without proof, citing
Carlsson–Mellit; proved here along Carlsson--Mellit's proof of `∇C_α(1) = D_α` (their Theorem 7.5,
from `𝒩(y_α) = q^{|α|-ℓ}N_α` and `𝒩 = ∇ω̄` on `V_0`). -/
theorem lhsOp_one_one_apply_one {nabla : Module.End K (Sym.Lambda K)}
    (hnab : IsMacdonaldConjugator 𝗊 𝗎 nabla) (hone : nabla 1 = 1) (α : List ℕ)
    (hpos : ∀ x ∈ α, 0 < x) :
    lhsOp 𝗊 𝗎 1 1 α 1 = (𝗊 ^ ((α.sum : ℤ) - (α.length : ℤ))) • nabla (CopComp 𝗊 α 1) := by
  have hq : (𝗊 : K) ≠ 0 := HJO.Standing.paramQ_ne_zero K
  have hM : (1 - 𝗊) * (1 - 𝗎) ≠ 0 := HJO.Standing.paramProduct_param_ne_zero K
  have hq1 : (1 : K) - 𝗊 ≠ 0 := left_ne_zero_of_mul hM
  set bar : K ≃+* K := (paramQUInv K).toRingEquiv with hbar_def
  have hbar : bar 𝗊 = 𝗊⁻¹ := paramQUInv_paramQ K
  have hbaru : bar 𝗎 = 𝗎⁻¹ := paramQUInv_paramU K
  have hbb : ∀ c : K, bar (bar c) = c := paramQUInv_involutive K
  obtain ⟨N, hN, -, -⟩ := exists_isConjugationOperator (q := 𝗊) (u := 𝗎) (bar := bar)
    (HJO.Standing.paramQ_add_one_ne_zero K) (HJO.Standing.paramQUInv_paramQ_eq_invOf K)
    (HJO.Standing.paramQUInv_paramU_eq_invOf K) hbb
  -- step 1: the conjugated word
  rw [lhsOp_one_one_apply_one_eq_lowerRunCM 𝗊 𝗎 hq α]
  -- step 2: it is `𝒩` of the lowered monomial
  have h0 := NRel.unFrom hN hq hq1 hbar α (NRel.one hN)
  rw [Nat.zero_add] at h0
  have hrel := NRel.lowerRunCM hN α.length h0
  have hval := lowerRunCM_unFrom_mul_C 𝗊 α hpos 1
  rw [map_one, mul_one] at hval
  rw [hval] at hrel
  set g : Sym.Lambda K := (-1) ^ α.length * bopComp 𝗊 α 1 with hg
  obtain ⟨hF, hG, e⟩ := hrel
  -- step 4: `𝒩 = ε_±∇ω̄` on `V_0`
  have hcomp := hnab.mem_lambdaComp hone hM
  have h74 := conjugation_eq_signGrading_conjugator_omegaBar hbb hbar hbaru hM hN hnab hcomp hone g
  have hv : vzero K g = ofPiece K 0 ⟨C g, hF⟩ := rfl
  rw [hv, e] at h74
  have hC := congrArg Subtype.val (ofPiece_injective _ h74)
  dsimp only at hC
  rw [hC]
  change constantCoeff (C (signGrading K (nabla (omegaBar bar g)))) = _
  rw [constantCoeff_C]
  -- step 3: `ω̄g = (-1)^ℓ(-q)^{N-ℓ}C_α(1)`
  have hω : omegaBar bar g
      = ((-1 : K) ^ α.length * (-𝗊) ^ ((α.sum : ℤ) - (α.length : ℤ))) • CopComp 𝗊 α 1 := by
    rw [hg, map_mul, omegaBar_bopComp hq hbar, map_one, map_pow, map_neg, map_one,
      show ((-1 : Sym.Lambda K) ^ α.length) = MvPolynomial.C ((-1 : K) ^ α.length) by simp,
      ← MvPolynomial.smul_eq_C_mul, smul_smul]
  have hlen := length_le_sum_of_forall_pos hpos
  have hmem := hcomp α.sum (CopComp 𝗊 α 1) (copComp_one_mem_lambdaComp 𝗊 rfl)
  rw [hω, map_smul, map_smul, signGrading_of_mem_lambdaComp hmem, smul_smul]
  congr 1
  obtain ⟨d, hd⟩ : ∃ d, α.sum = α.length + d := ⟨α.sum - α.length, by omega⟩
  rw [hd, show ((α.length + d : ℕ) : ℤ) - (α.length : ℤ) = (d : ℤ) by push_cast; ring,
    zpow_natCast, zpow_natCast, neg_pow, pow_add]
  ring_nf
  rw [show (-1 : K) ^ (α.length * 2) = 1 by rw [mul_comm, pow_mul, neg_one_sq, one_pow],
    show (-1 : K) ^ (d * 2) = 1 by rw [mul_comm, pow_mul, neg_one_sq, one_pow]]
  ring

end HJO.Mellit.LhsDesign
