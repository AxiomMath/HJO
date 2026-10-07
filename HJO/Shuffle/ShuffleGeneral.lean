/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.LhsOpAssembly
public import HJO.Shuffle.LhsOpBaseValue
public import HJO.Shuffle.BraidBECut

/-! # The compositional rational shuffle identity at every coprime `0 < a < b`

The shuffle side of the library is stated under the standing convention `1 < a < b`. The
convention `1 < a` is spent nowhere: each clause of Mellit's interface at the sweep witness holds
at every coprime `0 < a < b`, so the identity holds at `a = 1` as well.

* The left-hand side: `HJO.Mellit.LhsDesign.opClause_of_coprime_of_base` already reaches every
  coprime `a, b ≥ 1` from the base slope `(1, 1)`.
* `HJO.Mellit.mellitInduction_sweepWitness`: `HJO.Mellit.mellitInduction_of_sweepRecursionBEFloor`
  asks for `0 < a` and `a < b`, and `HJO.Mellit.braidValueColouring_sweepRecursionBEFloor` for
  `0 < a`, `0 < b`.
* `HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc` and
  `HJO.Mellit.sum_sweepChar_eq_sum_gessel` need only `0 < a`, `0 < b`.

## Main results

* `HJO.Mellit.lhsWord_standing_of_pos`: Mellit's left-hand side at the standing field, at every
  coprime `a, b ≥ 1`.
* `HJO.Mellit.mellitInduction_sweepWitness_of_lt`: `HJO.Mellit.mellitInduction_sweepWitness` at
  every coprime `0 < a < b`.
* `HJO.Mellit.aboveIdentity_of_lt`: the above-diagonal identity at every coprime `0 < a < b`.
* `HJO.Ascent.realisation_shuffle_eq_sum_of_lt`: the shuffle expansion, with the sign outside the
  realisation, at every coprime `0 < a < b`.

## Implementation notes

The range `b ≤ a` (including `a = b = 1`) is not reached. Two steps of the braid evaluation use
`a < b` essentially: the type-`C` letter, through
`HJO.Mellit.Isolates.pointRank_lt_add_of_eventType_C_of_lt` (the attack window `ω` must be at most
`b(aN+1)N - 1`), and the append setup `HJO.Mellit.IsAppendSetup`, whose field `a_lt_b` is used to
bound `1/(a+b)` below `1/2` and to compare `a + 1 ≤ b`.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open HJO.Sym HJO.Sweep HJO.Ascent ParkingFunctions Paths

/-- **Mellit's left-hand side at the standing field, at every coprime `a, b ≥ 1`.** -/
theorem lhsWord_standing_of_pos {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) :
    LhsWord (paramQ Kk) (paramU Kk) a b :=
  LhsDesign.lhsWord_of_opClause (LhsDesign.opClause_of_coprime_of_base Kk
    (fun hnab hone α hpos => LhsDesign.lhsOp_one_one_apply_one Kk hnab hone α hpos) a b hab ha hb)

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`LhsComputes` at every algebraically independent pair and every coprime `a, b ≥ 1`.** -/
theorem lhsComputes_of_pos {q u : L} (hqu : AlgebraicIndependent ℤ ![q, u]) {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) : LhsComputes q u a b :=
  lhsComputes_of_lhsWord (lhsWord_ascend Kk hqu (lhsWord_standing_of_pos hab ha hb))

/-- **`HJO.Mellit.mellitInduction_sweepWitness` at the sweep witness, at every coprime
`0 < a < b`.** -/
theorem mellitInduction_sweepWitness_of_lt {q u : L} (hqu : AlgebraicIndependent ℤ ![q, u])
    {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (hlt : a < b) :
    MellitInduction (sweepWitness q u a b) a b := by
  let _ : Algebra ℚ (AlgebraicClosure L) :=
    ((algebraMap L (AlgebraicClosure L)).comp (algebraMap ℚ L)).toAlgebra
  refine mellitInduction_of_algebraMap (K := AlgebraicClosure L) hab ha ?_
  have hqu' : AlgebraicIndependent ℤ
      ![algebraMap L (AlgebraicClosure L) q, algebraMap L (AlgebraicClosure L) u] := by
    have h := hqu.map' (f := (algebraMap L (AlgebraicClosure L)).toIntAlgHom)
      (algebraMap L (AlgebraicClosure L)).injective
    convert h using 1
    · funext i
      fin_cases i <;> rfl
    · exact Subsingleton.elim _ _
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_eq_mul_self (algebraMap L (AlgebraicClosure L) q)
  have hq := ne_zero_of_algebraicIndependent_fst hqu'
  have hq1 := ne_one_of_algebraicIndependent_fst hqu'
  have hqp := add_one_ne_zero_of_algebraicIndependent_fst hqu'
  have hu := ne_zero_of_algebraicIndependent_snd hqu'
  exact mellitInduction_of_sweepRecursionBEFloor hq hq1 hqp hr.symm hu hab ha hlt
    fun N hN => braidValueColouring_sweepRecursionBEFloor _ _ hq hq1 hqp hr.symm hu ha
      (by omega) hN hlt

/-- **The above-diagonal identity, with reflected descent sets, at every coprime `0 < a < b`.** -/
theorem aboveIdentity_of_lt {q u : L} (hqu : AlgebraicIndependent ℤ ![q, u]) {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : 0 < a) (hlt : a < b)
    {ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L} (hι : Sym.IsRealisation ι)
    {Θ : Sym.Lambda L →ₐ[L] Module.End L (Sym.Lambda L)} (hΘ : Sym.IsSlopeHom a b q u Θ)
    {N : ℕ} (hN : 0 < N) {α : List ℕ} (hαpos : ∀ x ∈ α, 0 < x) (hαN : α.sum = N) :
    (-1 : L) ^ (N * (b + 1)) • ι (Θ (Sym.CopComp q α 1) 1)
      = ∑ π ∈ aboveWithReturns α a b N,
          (q ^ aboveDinv π * u ^ Paths.aboveArea (abovePath π)) •
            gessel L (b * N) (descentReverse (b * N) (aboveIdes π)) := by
  have hb : 0 < b := by omega
  exact aboveIdentity_of_mellit (sweepWitness q u a b)
    ((lhsRewrite_sweepWitness_iff_lhsComputes hab ha hb).2 (lhsComputes_of_pos hqu hab ha hb))
    (mellitInduction_sweepWitness_of_lt hqu hab ha hlt)
    (rem41_of_sweepComputes _ hab ha hb (fun _ _ _ _ => rfl)
      (fun N η α hpos hsum => sweepWitness_proj_dminus_pow_D q u ha hb N η hpos hsum)
      (sweepComputes_of_algebraicIndependent q u hqu a b))
    (rhsSumsAgree_sweepWitness ha (ne_zero_of_algebraicIndependent_fst hqu))
    (ne_zero_of_algebraicIndependent_snd hqu) ι hι Θ hΘ N hN α hαpos hαN

end HJO.Mellit

namespace HJO.Ascent

open HJO.Sym HJO.ParkingFunctions HJO.Paths

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The compositional rational shuffle expansion at algebraically independent parameters, at
every coprime `0 < a < b`**, with the sign outside the realisation: in particular at `a = 1`. -/
theorem realisation_shuffle_eq_sum_of_lt {x y : L} (hxy : AlgebraicIndependent ℤ ![x, y])
    {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (hlt : a < b)
    {ι : Lambda L →ₐ[L] AlphabetSeries L} (hι : IsRealisation ι)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom a b x y Θ) {N : ℕ} (hN : 0 < N)
    {α : List ℕ} (hαpos : ∀ r ∈ α, 0 < r) (hαN : α.sum = N) :
    (-1 : L) ^ (N * (b + 1)) • ι (Θ (CopComp x α 1) 1) =
      ∑ π ∈ withReturns α.reverse a b N,
        (x ^ dinv π * y ^ area (path π)) • gessel L (b * N) (ides π) := by
  have hrev := gesselReverseSum L
  -- the above-diagonal identity, descent sets reflected back
  have hmain := Mellit.aboveIdentity_of_lt hxy hab ha hlt hι hΘ hN hαpos hαN
  have hf : ι ((-1 : L) ^ (N * (b + 1)) • Θ (CopComp x α 1) 1)
      = ∑ π ∈ aboveWithReturns α a b N,
          (x ^ aboveDinv π * y ^ aboveArea (abovePath π)) •
            gessel L (b * N) (descentReverse (b * N) (aboveIdes π)) := by
    rw [map_smul]
    exact hmain
  have habove := hrev ι hι (b * N) _ (aboveWithReturns α a b N)
    (fun π => x ^ aboveDinv π * y ^ aboveArea (abovePath π))
    (fun π => descentReverse (b * N) (aboveIdes π))
    (fun π _ => descentReverse_subset_Ico (aboveIdes_subset π)) _ hf
  rw [map_smul] at habove
  have habove' : (-1 : L) ^ (N * (b + 1)) • ι (Θ (CopComp x α 1) 1)
      = ∑ π ∈ aboveWithReturns α a b N,
          (x ^ aboveDinv π * y ^ aboveArea (abovePath π)) •
            gessel L (b * N) (aboveIdes π) := by
    rw [habove]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [descentReverse_descentReverse
      ((aboveIdes_subset π).trans Finset.Ico_subset_Iic_self)]
  -- the half turn, then the reflection once more
  have hg : ι ((-1 : L) ^ (N * (b + 1)) • Θ (CopComp x α 1) 1)
      = ∑ π ∈ withReturns α.reverse a b N, (x ^ dinv π * y ^ area (path π)) •
          gessel L (b * N) (descentReverse (b * N) (ides π)) := by
    rw [map_smul, habove']
    exact sum_aboveWithReturns_eq ha hN x y α
  have hres := hrev ι hι (b * N) (ParkingFunction a b N) (withReturns α.reverse a b N)
    (fun π => x ^ dinv π * y ^ area (path π))
    (fun π => descentReverse (b * N) (ides π))
    (fun π _ => descentReverse_subset_Ico (ides_subset π)) _ hg
  rw [map_smul] at hres
  rw [hres]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [descentReverse_descentReverse ((ides_subset π).trans Finset.Ico_subset_Iic_self)]

end HJO.Ascent
