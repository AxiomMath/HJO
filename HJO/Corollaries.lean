/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Determinant.DetCoeffSolves
public import HJO.CylindricProduct.Summable
public import HJO.Macdonald.PieriSupportFull
public import HJO.Collinear.PfunSupportDischarge
public meta import HJO.Attr

/-! # Short corollaries of the determinant, kernel, operator, Macdonald and gap theories

This file collects seven statements each of which is a short consequence of results proved
elsewhere in the library.

* The truncated determinant `𝒟_H(s;q) = det(I - L_H(s,q))` only has monomials whose `s`-degree is
  divisible by `d = a + b`: in its Leibniz expansion only the permutations moving every vertex
  along an edge survive, such a permutation is a product of cycles of length `d`, and its term has
  `s`-degree the number of vertices it moves.
* For `H, H' ≥ a(D+1) + ab` the `q^D`-coefficient of any `s`-coefficient of `𝒟_H` and `𝒟_{H'}`
  agree.
* The basic operators `D_k` are `𝕜`-linear.
* A coercive kernel has a trace: its diagonal is summable.
* Every `𝕜`-basis of `Λ` that is an eigenbasis of `D_0` with eigenvalues `-(M B_μ - 1)` has
  one-cell Pieri support on the covers.
* A modified Macdonald family exists at `𝕜 = ℚ(q, u)`.
* The polarisation of the quadratic form `Q` of the gap set at a finite sum of vectors.

## Main results

* `HJO.DetLimit.coeff_det_one_sub_weightedAdjacency_eq_zero`.
* `HJO.DetLimit.coeff_coeff_det_one_sub_weightedAdjacency_eq`.
* `HJO.Sym.isLinearMap_dop`.
* `HJO.CylindricProduct.traceSummable_of_gradeBdd`.
* `HJO.Standing.elemSymm_one_mul_mem_span_of_dop_zero_param`.
* `HJO.Standing.exists_isModifiedMacdonaldFamily_param'`.
* `HJO.Gaps.q_sum_eq`.

## Implementation notes

The truncated determinant is read in the model `ℚ((q))[s]` of `HJO.Determinant.detTrunc`, as
`(1 - weightedAdjacency a b H).det`; the coefficient of `q^D s^n` is the `D`-th Laurent coefficient
of its `s^n`-coefficient. The stabilisation is stated for every `s`-degree `n`, not only for the
degrees `dk`, which is no stronger in substance by the first result. The usual standing
hypothesis on `a` and `b` is `1 < a < b` coprime; only `0 < a` and `0 < b` (and coprimality for the
first result) are used.

Coerciveness of a kernel is the predicate `HJO.CylindricProduct.GradeBdd`.

The Macdonald statements are made at the standing field `K`, a fraction field of the parameter ring
`ℚ[q^{±1}, u^{±1}]`, with `q = paramQ K` and `u = paramU K`.
-/

@[expose] public section

open Finset

/-! ### The truncated determinant -/

namespace HJO.DetLimit

open Determinant DetEquation DetCoeffSolves

/-- An edge permutation moves a multiple of `d = a + b` vertices: each of its cycles has
length `d`. -/
theorem dvd_card_support_of_isEdgePerm {a b H : ℕ} (hab : Nat.Coprime a b) (hb : 0 < b)
    {σ : Equiv.Perm (Fin (H + 1))} (hσ : IsEdgePerm a b H σ) : a + b ∣ σ.support.card := by
  rw [← Equiv.Perm.sum_cycleType]
  refine Multiset.dvd_sum fun n hn => ?_
  rw [Equiv.Perm.cycleType_def, Multiset.mem_map] at hn
  obtain ⟨c, hc, rfl⟩ := hn
  exact (card_support_of_mem_cycleFactorsFinset hab hb hσ hc).symm.dvd

/-- **The truncated determinant is a series in `s^d`.** For coprime positive
`a, b`, the coefficient of `s^n` in `𝒟_H(s;q) = det(I - L_H(s,q))` vanishes unless `d = a + b`
divides `n`. -/
@[hjo "lem_det_s_degree"]
theorem coeff_det_one_sub_weightedAdjacency_eq_zero {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : 0 < a) (hb : 0 < b) (H : ℕ) {n : ℕ} (hn : ¬ a + b ∣ n) :
    (1 - weightedAdjacency a b H).det.coeff n = 0 := by
  rw [det_one_sub_weightedAdjacency, Polynomial.coeff_map, intDet,
    DetCoeffSolves.det_eq_sum_perm, Polynomial.finsetSum_coeff, Finset.sum_eq_zero, map_zero]
  intro σ _
  rw [Polynomial.coeff_C_mul]
  by_cases hσ : IsEdgePerm a b H σ
  · have hne : n ≠ σ.support.card := fun h => hn (h ▸ dvd_card_support_of_isEdgePerm hab hb hσ)
    rw [prod_intOneSub a b H ha hb hσ, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp [hne]
  · rw [prod_intOneSub_eq_zero a b H hσ, Polynomial.coeff_zero, mul_zero]

/-- **The coefficients stabilise.** For positive `a, b`, `D ≥ 0` and
`H, H' ≥ a(D+1) + ab`, the coefficient of `q^D s^n` in `𝒟_H(s;q)` equals that in `𝒟_{H'}(s;q)`,
for every `n`, in particular for `n = dk`. -/
@[hjo "lem_det_coeff_stable"]
theorem coeff_coeff_det_one_sub_weightedAdjacency_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (n D : ℕ) {H H' : ℕ} (hH : a * (D + 1) + a * b ≤ H) (hH' : a * (D + 1) + a * b ≤ H') :
    ((1 - weightedAdjacency a b H).det.coeff n).coeff (D : ℤ)
      = ((1 - weightedAdjacency a b H').det.coeff n).coeff (D : ℤ) := by
  have hab : b ≤ a * b := Nat.le_mul_of_pos_left b ha
  rw [det_one_sub_weightedAdjacency, det_one_sub_weightedAdjacency, Polynomial.coeff_map,
    Polynomial.coeff_map, qOfRat, HahnSeries.ofPowerSeries_apply_coeff,
    HahnSeries.ofPowerSeries_apply_coeff, ← coeff_limCoeff a b n D ha hb (by omega),
    ← coeff_limCoeff a b n D ha hb (by omega)]

end HJO.DetLimit

/-! ### The basic operators are linear -/

namespace HJO.Sym

/-- **The basic operators are linear.** For every `k ≥ 0` the map `D_k` is
`𝕜`-linear from `Λ` to `Λ`. -/
@[hjo "lem_dop_linear"]
theorem isLinearMap_dop {L : Type*} [Field L] [Algebra ℚ L] (q u : L) (k : ℕ) :
    IsLinearMap L (Dop q u k) :=
  ⟨fun f g => (Dop q u k).map_add f g, fun c f => (Dop q u k).map_smul c f⟩

end HJO.Sym

/-! ### A coercive kernel has a trace -/

namespace HJO.CylindricProduct

/-- **A coercive kernel has a trace.** If every entry `K λ ν` is divisible
by `q ^ |λ|`, then the diagonal family `λ ↦ K λ λ` is summable, which is the side condition of the
kernel trace. -/
@[hjo "lem_coercive_trace"]
theorem traceSummable_of_gradeBdd {K : Kernel} (hK : GradeBdd K) : TraceSummable K :=
  summable_of_dvd_of_finite (g := fun lam : Part => lam.size) (fun lam => hK lam lam)
    finite_size_le

end HJO.CylindricProduct

/-! ### The modified Macdonald family -/

namespace HJO.Standing

open HJO.Sym HJO.Ascent

variable (K : Type*) [Field K] [Algebra ℚ K] [Algebra ParamRing K] [IsFractionRing ParamRing K]

/-- **The support of the Pieri expansion.** At `𝕜 = ℚ(q, u)`, let
`(H̃_μ)` be a `𝕜`-basis of `Λ` with `D_0 H̃_μ = -(M B_μ - 1) H̃_μ` for every `μ`. Then for every
`ν`, `e₁ H̃_ν` lies in the `𝕜`-span of the `H̃_μ` with `μ` covering `ν`. -/
@[hjo "lem_ght2_pieri_support"]
theorem elemSymm_one_mul_mem_span_of_dop_zero_param {H : YoungDiagram → Lambda K}
    (hH : LinearIndependent K H) (hHsp : Submodule.span K (Set.range H) = ⊤)
    (hHdop : ∀ μ, Dop (paramQ K) (paramU K) 0 (H μ)
      = -(paramProduct (paramQ K) (paramU K) * cellSum (paramQ K) (paramU K) μ - 1) • H μ)
    (ν : YoungDiagram) :
    elemSymm K 1 * H ν ∈ Submodule.span K (H '' {μ : YoungDiagram | Covers μ ν}) :=
  elemSymm_one_mul_mem_of_dop_zero (algebraicIndependent_param K)
    (linearIndependent_macHtilde_param K) (dop_zero_smul_macHtilde_param K)
    (elemSymm_one_mul_macHtilde_mem_span_param K) hH hHsp hHdop ν

/-- **A modified Macdonald family exists** at `𝕜 = ℚ(q, u)`. -/
@[hjo "lem_ght_family_exists"]
theorem exists_isModifiedMacdonaldFamily_param' :
    ∃ H : YoungDiagram → Lambda K, IsModifiedMacdonaldFamily (paramQ K) (paramU K) H :=
  exists_isModifiedMacdonaldFamily_of_hasPieriEigenfamily (algebraicIndependent_param K)
    (paramQUInvHom_paramQ K) (paramQUInvHom_paramU K) (paramQUInvHom_involutive K)
    (Sym.ringHom_algebraMap_rat (paramQUInvHom K)) (hasUnnormalisedMacdonaldEigenbasis_param K)
    (hasPieriEigenfamily_param K (hasPfunPieriSupport_param K))

end HJO.Standing

/-! ### The quadratic form at a sum of gap vectors -/

namespace HJO.Gaps

open NumericalSemigroup

/-- Splitting a square double sum into its diagonal and its pairs `p < r`. -/
theorem sum_sum_eq_sum_add_sum_Ioi {M : Type*} [AddCommMonoid M] {N : ℕ} (f : Fin N → Fin N → M) :
    ∑ p, ∑ r, f p r = ∑ p, f p p + ∑ p, ∑ r ∈ Ioi p, (f p r + f r p) := by
  calc ∑ p, ∑ r, f p r = ∑ r, ∑ p, f p r := Finset.sum_comm
    _ = ∑ r, (f r r + ∑ p ∈ {r}ᶜ, f p r) := Finset.sum_congr rfl fun r _ => by
          rw [← Finset.sum_compl_add_sum {r}, Finset.sum_singleton, add_comm]
    _ = ∑ p, f p p + ∑ p, ∑ r ∈ Ioi p, (f p r + f r p) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_sum_Ioi_add_eq_sum_sum_off_diag]
          simp_rw [add_comm (f _ _) (f _ _)]

/-- **The quadratic form at a sum of gap vectors.** For `x_1, …, x_N ∈ ℤ^G`,
`Q(∑ x_p) = ∑ Q(x_p) + ∑_{p < r} ∑_{g, h ∈ G} (K(h - g) + K(g - h)) x_{p,g} x_{r,h}`. -/
@[hjo "lem_ret_form_sum"]
theorem q_sum_eq (a b : ℕ) {N : ℕ} (x : Fin N → (finspan {a, b}).gaps → ℤ) :
    HJO.Q a b (∑ p, x p) = ∑ p, HJO.Q a b (x p) +
      ∑ p, ∑ r ∈ Ioi p, ∑ g : (finspan {a, b}).gaps, ∑ h : (finspan {a, b}).gaps,
        (HJO.U a b ((h : ℕ) - (g : ℕ)) + HJO.U a b ((g : ℕ) - (h : ℕ))) * x p g * x r h := by
  set B : Fin N → Fin N → ℤ := fun p r => ∑ g : (finspan {a, b}).gaps,
    ∑ h : (finspan {a, b}).gaps, HJO.U a b ((h : ℕ) - (g : ℕ)) * x p g * x r h with hB
  have hQ : HJO.Q a b (∑ p, x p) = ∑ p, ∑ r, B p r := by
    have hexp : ∀ g h : (finspan {a, b}).gaps,
        HJO.U a b ((h : ℕ) - (g : ℕ)) * (∑ p, x p) g * (∑ p, x p) h
          = ∑ p, ∑ r, HJO.U a b ((h : ℕ) - (g : ℕ)) * x p g * x r h := by
      intro g h
      rw [Finset.sum_apply, Finset.sum_apply, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
      simp_rw [Finset.mul_sum, mul_assoc]
    rw [q_eq_sum_sum]
    simp_rw [hexp, hB]
    calc ∑ g : (finspan {a, b}).gaps, ∑ h : (finspan {a, b}).gaps, ∑ p, ∑ r,
          HJO.U a b ((h : ℕ) - (g : ℕ)) * x p g * x r h
        = ∑ g : (finspan {a, b}).gaps, ∑ p, ∑ h : (finspan {a, b}).gaps, ∑ r,
          HJO.U a b ((h : ℕ) - (g : ℕ)) * x p g * x r h :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ p, ∑ g : (finspan {a, b}).gaps, ∑ h : (finspan {a, b}).gaps, ∑ r,
          HJO.U a b ((h : ℕ) - (g : ℕ)) * x p g * x r h := Finset.sum_comm
      _ = ∑ p, ∑ g : (finspan {a, b}).gaps, ∑ r, ∑ h : (finspan {a, b}).gaps,
          HJO.U a b ((h : ℕ) - (g : ℕ)) * x p g * x r h :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ p, ∑ r, ∑ g : (finspan {a, b}).gaps, ∑ h : (finspan {a, b}).gaps,
          HJO.U a b ((h : ℕ) - (g : ℕ)) * x p g * x r h :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [hQ, sum_sum_eq_sum_add_sum_Ioi]
  congr 1
  · exact Finset.sum_congr rfl fun p _ => (q_eq_sum_sum a b (x p)).symm
  · refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
    simp only [hB]
    rw [Finset.sum_comm (f := fun (g h : (finspan {a, b}).gaps) =>
        HJO.U a b ((h : ℕ) - (g : ℕ)) * x r g * x p h),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun h _ => by ring

end HJO.Gaps
