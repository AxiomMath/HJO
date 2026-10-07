/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.DpaStructure
public import HJO.CMStructure.Thm73Closed
public meta import HJO.Attr

/-! # The structure of the double module over `𝕜 = ℚ(q, u)`

Over the standing coefficient field `𝕜 = ℚ(q, u)`, with `q` and `u` indeterminates, the extended
Dyck path algebra `Ã` acts on `V_* = ⨁_k V_k` by the operators of Carlsson and Mellit, the kernel
of `Ã𝟏_0 → V_*`, `fe_0 ↦ f(1)`, is the ideal `I𝟏_0`, and for Mellit's modified pair the kernel is
`𝓘` and the induced map `Ã𝟏_0/𝓘 → V_*` is bijective. These are Theorem 7.3 of Carlsson and Mellit
and Theorem 3.6 of Mellit, with no hypothesis on the coefficients.

Over a general field the proofs use a ring involution of the coefficients inverting `q` and `u`, as
in `HJO.Sym.paramInvLambda`, through the star swap of `Ã`. Over `𝕜` that involution exists: it is
the automorphism `ι = HJO.Sym.paramQUInv` sending `q ↦ q⁻¹` and `u ↦ u⁻¹`. The nonvanishing of `q`,
`u`, `q - 1` and `q + 1` follows from the algebraic independence of `q` and `u`.

## Main results

* `HJO.Standing.exists_action_atilde_ker_eq_param`.
* `HJO.Standing.atildeE0_inf_ker_evalOne_eq_param`.
* `HJO.Standing.dpaStructure_param`.

## Implementation notes

The field `𝕜` is any field `K` presented as a field of fractions of `ℚ[q, u]`, with `q` and `u`
the images `HJO.Ascent.paramQ K`, `HJO.Ascent.paramU K` of the indeterminates. The invertibility of
`q`, `q - 1` and `u`, which the operators are defined with, is supplied by instances below.
The general-field statements, which assume the involution, are `HJO.Sweep.dpaStructure`,
`HJO.Sweep.atildeE0_inf_ker_evalOne_eq` and `HJO.Sweep.exists_action_atilde_ker_eq`.

## References

The statements `HJO.Standing.dpaStructure_param`, `HJO.Standing.atildeE0_inf_ker_evalOne_eq_param`,
`HJO.Standing.exists_action_atilde_ker_eq_param`; Carlsson and Mellit, *A proof of the shuffle
conjecture*, Theorem 7.3; Mellit, *Toric braids and (m, n)-parking functions*, Theorem 3.6.
-/

@[expose] public section

namespace HJO.Standing

open HJO.Ascent HJO.Sym HJO.Sweep Dyck.Tilde

variable (K : Type*) [Field K] [Algebra ParamRing K] [IsFractionRing ParamRing K]

/-- `q + 1 ≠ 0` at the standing field. -/
theorem paramQ_add_one_ne_zero : paramQ K + 1 ≠ 0 := by
  have := aeval_ne_zero_of_witness (algebraicIndependent_param K) (P := MvPolynomial.X 0 + 1)
    ![0, 0] (by simp)
  simpa using this

/-- `q - 1 ≠ 0` at the standing field. -/
theorem paramQ_sub_one_ne_zero : paramQ K - 1 ≠ 0 := by
  rw [← neg_ne_zero, neg_sub]
  exact one_sub_q_ne_zero (algebraicIndependent_param K)

/-- The parameter `q` is invertible in the standing field. -/
noncomputable instance invertibleParamQ : Invertible (paramQ K) :=
  invertibleOfNonzero (paramQ_ne_zero K)

/-- The element `q - 1` is invertible in the standing field. -/
noncomputable instance invertibleParamQSubOne : Invertible (paramQ K - 1) :=
  invertibleOfNonzero (paramQ_sub_one_ne_zero K)

/-- The parameter `u` is invertible in the standing field. -/
noncomputable instance invertibleParamU : Invertible (paramU K) :=
  invertibleOfNonzero (paramU_ne_zero K)

variable [Algebra ℚ K]

/-- The inversion `ι` of both parameters sends `q` to `⅟q`. -/
theorem paramQUInv_paramQ_eq_invOf :
    (paramQUInv K).toRingEquiv (paramQ K) = ⅟(paramQ K) := by
  rw [invOf_eq_inv]; exact paramQUInv_paramQ K

/-- The inversion `ι` of both parameters sends `u` to `⅟u`. -/
theorem paramQUInv_paramU_eq_invOf :
    (paramQUInv K).toRingEquiv (paramU K) = ⅟(paramU K) := by
  rw [invOf_eq_inv]; exact paramQUInv_paramU K

/-- **`HJO.Standing.atildeE0_inf_ker_evalOne_eq_param` over `𝕜`: the kernel of `Ãe_0 → V_*` is
`Ie_0`.** For every action of `Ã` on `V_*` by the operators of Carlsson and Mellit, the kernel of
`fe_0 ↦ f(1)` on `Ã𝟏_0` is `I𝟏_0`. -/
@[hjo "lem_cm_kernel_exact"]
theorem atildeE0_inf_ker_evalOne_eq_param
    (ρ : Atilde K (paramQ K) (paramU K) →ₐ[K] Module.End K (Vstar K))
    (hρe : ∀ k : ℕ, ρ (Atilde.e K (paramQ K) (paramU K) k) = pieceProj K k)
    (hρT : ∀ k i : ℕ,
      ρ (Atilde.Tg K (paramQ K) (paramU K) k i) = loopVstar (braidModPiece (paramQ K)) k i)
    (hρd : ∀ k : ℕ,
      ρ (Atilde.dMinus K (paramQ K) (paramU K) k) = lowerVstar (dminusPiece (paramQ K)) k)
    (hρup : ∀ k : ℕ,
      ρ (Atilde.dPlus K (paramQ K) (paramU K) k) = raiseVstar (cmDPlusPiece (paramQ K)) k)
    (hρupStar : ∀ k : ℕ, ρ (Atilde.dPlusStar K (paramQ K) (paramU K) k)
      = raiseVstar (dplusStarPiece (paramQ K) (paramU K)) k) :
    Atilde.atildeE0 K (paramQ K) (paramU K) ⊓ LinearMap.ker (evalOne ρ)
      = Atilde.kernelIdealE0 K (paramQ K) (paramU K) :=
  atildeE0_inf_ker_evalOne_eq (paramQUInv_paramQ_eq_invOf K) (paramQUInv_paramU_eq_invOf K)
    (paramQUInv_involutive K) ρ hρe hρT hρd hρup hρupStar

/-- **`HJO.Standing.exists_action_atilde_ker_eq_param` over `𝕜`: Carlsson and Mellit's
Theorem 7.3.** The operators `T_i`, `d_-`, `d_+`, `d^*_+` and the projections onto the summands
define an action of `Ã` on `V_*`, and the kernel of `Ãe_0 → V_*`, `fe_0 ↦ f(1)`, is `Ie_0`. -/
@[hjo "lem_cm_thm73"]
theorem exists_action_atilde_ker_eq_param :
    ∃ ρ : Atilde K (paramQ K) (paramU K) →ₐ[K] Module.End K (Vstar K),
      (∀ k : ℕ, ρ (Atilde.e K (paramQ K) (paramU K) k) = pieceProj K k)
      ∧ (∀ k i : ℕ,
          ρ (Atilde.Tg K (paramQ K) (paramU K) k i) = loopVstar (braidModPiece (paramQ K)) k i)
      ∧ (∀ k : ℕ,
          ρ (Atilde.dMinus K (paramQ K) (paramU K) k) = lowerVstar (dminusPiece (paramQ K)) k)
      ∧ (∀ k : ℕ,
          ρ (Atilde.dPlus K (paramQ K) (paramU K) k) = raiseVstar (cmDPlusPiece (paramQ K)) k)
      ∧ (∀ k : ℕ, ρ (Atilde.dPlusStar K (paramQ K) (paramU K) k)
          = raiseVstar (dplusStarPiece (paramQ K) (paramU K)) k)
      ∧ Atilde.atildeE0 K (paramQ K) (paramU K) ⊓ LinearMap.ker (evalOne ρ)
          = Atilde.kernelIdealE0 K (paramQ K) (paramU K) :=
  exists_action_atilde_ker_eq (paramQUInv_paramQ_eq_invOf K) (paramQUInv_paramU_eq_invOf K)
    (paramQUInv_involutive K) (paramQ_add_one_ne_zero K)

/-- **`HJO.Standing.dpaStructure_param` over `𝕜`: Mellit, the structure of the double module.** The
modified pair `(ρ^♭, ρ^{♭*})` defines an action `ρ` of `Ã` on `V_*`; the kernel of
`φ : Ã𝟏_0 → V_*, x ↦ ρ(x)(1)` is `𝓘`; and the induced map `Ã𝟏_0/𝓘 → V_*` is a linear
isomorphism. -/
@[hjo "thm_dpa_structure"]
theorem dpaStructure_param :
    ∃ ρ : Atilde K (paramQ K) (paramU K) →ₐ[K] Module.End K (Vstar K),
      (∀ k : ℕ, ρ (Atilde.e K (paramQ K) (paramU K) k) = pieceProj K k)
      ∧ (∀ k i : ℕ,
          ρ (Atilde.Tg K (paramQ K) (paramU K) k i) = loopVstar (braidModPiece (paramQ K)) k i)
      ∧ (∀ k : ℕ, ρ (Atilde.dMinus K (paramQ K) (paramU K) k)
          = lowerVstar (dminusModPiece (paramQ K)) k)
      ∧ (∀ k : ℕ, ρ (Atilde.dPlus K (paramQ K) (paramU K) k)
          = raiseVstar (dplusModPiece (paramQ K)) k)
      ∧ (∀ k : ℕ, ρ (Atilde.dPlusStar K (paramQ K) (paramU K) k)
          = raiseVstar (dplusStarPiece (paramQ K) (paramU K)) k)
      ∧ LinearMap.ker ((evalOne ρ).domRestrict (Atilde.atildeE0 K (paramQ K) (paramU K)))
          = ((Atilde.mellitKernel K (paramQ K) (paramU K)).restrictScalars K).comap
              (Atilde.atildeE0 K (paramQ K) (paramU K)).subtype
      ∧ ∃ e : (Atilde.atildeE0 K (paramQ K) (paramU K) ⧸
            ((Atilde.mellitKernel K (paramQ K) (paramU K)).restrictScalars K).comap
              (Atilde.atildeE0 K (paramQ K) (paramU K)).subtype) ≃ₗ[K] Vstar K,
          ∀ x : Atilde.atildeE0 K (paramQ K) (paramU K),
            e (Submodule.Quotient.mk x) = evalOne ρ x :=
  dpaStructure (paramQ K) (paramU K) (paramQ_add_one_ne_zero K) (paramQUInv_paramQ_eq_invOf K)
    (paramQUInv_paramU_eq_invOf K) (paramQUInv_involutive K)

end HJO.Standing

end
