/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.AddLetter
public import HJO.CarlssonMellit.ThetaCommute
public meta import HJO.Attr

/-! # The `(q-1)`-plethysm turns a virtual letter into a letter

The raising recursion of Carlsson and Mellit expands a character in powers of the last auxiliary
variable, and the paper's substitution `X ↦ X + y_{k+1}` on the *unnormalised* side has to be
matched against the substitution `X ↦ X + (q-1)y_{k+1}` that the raising operator `d_+` performs.
The two are conjugate under the plethysm `θ` of `HJO.Sweep.theta`, which is the normalisation of
`HJO.Dyck.IsSigmaCharacter`, and this file proves that conjugation:
`ρ_{k+1} ∘ θ_k = θ_{k+1} ∘ τ_{k+1,k+1}`.

## Main results

* `HJO.Sweep.addLetter_theta`,
  `ρ_{k+1}(θ_k(G)) = θ_{k+1}(τ_{k+1,k+1}(G))`.

## Implementation notes

**No membership hypothesis is needed, and none is carried.** The paper states the identity for
`G ∈ V_k`, the right-hand side being formed after the inclusion `V_k ⊆ V_{k+1}`. In this library
`θ`, `τ` and `ρ` are endomorphisms of the one total space `HJO.Sweep.Total L`
(`HJO/Shuffle/SweepModule.lean` explains why), so that inclusion is the identity map and the
identity proved below holds for every `F : Total L`. That is strictly stronger than the paper's
statement, and it is the shape `HJO.Dyck.isSigmaCharacter_cmDPlus` consumes; the domain and codomain
are `HJO.Sweep.theta_mem_piece` and `HJO.Sweep.addLetter_mem_piece_succ`, already proved elsewhere.

**Why the identity is true, and where the exponent enters.** Both composites are `𝕜[y]`-algebra
endomorphisms, so `MvPolynomial.algHom_ext'` reduces the claim to the auxiliary variables — which
all three maps fix — and to the power sums, where
`θ_k(p_r) = (q^r-1)p_r ↦ (q^r-1)(p_r + y_{k+1}^r)` on the left and
`τ_{k+1,k+1}(p_r) = p_r + (q^r-1)y_{k+1}^r ↦ (q^r-1)p_r + (q^r-1)y_{k+1}^r` on the right, the
letter `y_{k+1}` being fixed by `θ_{k+1}`. The two agree because the *same* scalar `q^r - 1` occurs
in `θ` and in `τ`: under the monomial reading `p_r ↦ p_r + (q-1)^ry_i^r` of `HJO.Sweep.qshift` the
right-hand side would carry `(q-1)^r` where the left carries `q^r-1`, and the identity would fail
from `r = 2` on. This is the one place in this part of the library where the virtual reading of
the letter `(q-1)y_i` is forced by a comparison rather than by a computation inside the paper.

## References

This file proves `HJO.Sweep.addLetter_theta`, with the definitions `HJO.Sweep.piece`,
`HJO.Sweep.qshift`, `HJO.Sweep.addLetter` and `HJO.Sweep.theta`; used by
`HJO.Dyck.isSigmaCharacter_cmDPlus`. E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*,
J. Amer. Math. Soc. **31** (2018) 661--697, §5.
-/

@[expose] public section

namespace HJO.Sweep

variable {L : Type*} [Field L]

/-- **The `(q-1)`-plethysm turns a virtual letter into a letter.**
`ρ_{k+1}(θ_k(G)) = θ_{k+1}(τ_{k+1,k+1}(G))`: adding the genuine letter `y_{k+1}` after the plethysm
is the same as adding the virtual letter `(q-1)y_{k+1}` before it.

The hypothesis `G ∈ V_k` is not needed: all three maps are endomorphisms of the one
total space, the inclusion `V_k ⊆ V_{k+1}` of the statement is the identity here, and
the identity below holds at every `F`. Both composites are `𝕜[y]`-algebra endomorphisms, so it is
enough to compare on the auxiliary variables, which all three maps fix, and on the power sums,
where both give `(q^r-1)p_r + (q^r-1)y_{k+1}^r`. -/
@[hjo "lem_cm_theta_addletter"]
theorem addLetter_theta (q : L) (k : ℕ) (F : Total L) :
    addLetter L (k + 1) (theta q F) = theta q (qshift q (k + 1) F) := by
  have key : (addLetter L (k + 1)).comp (theta q) = (theta q).comp (qshift q (k + 1)) := by
    refine MvPolynomial.algHom_ext' ?_ fun n => ?_
    · refine MvPolynomial.algHom_ext fun r => ?_
      have hC : (algebraMap (Sym.Lambda L) (Total L)) (MvPolynomial.X r)
          = MvPolynomial.C (Sym.powerSum L (r + 1)) := by
        simp [Sym.powerSum]
      have hscal : (scal (q ^ (r + 1) - 1) : Total L)
          = algebraMap L (Total L) (q ^ (r + 1) - 1) := rfl
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hC, theta_powerSum,
        qshift_powerSum, hscal, map_add, map_mul, map_pow, AlgHom.commutes,
        addLetter_powerSum, theta_powerSum, theta_auxVar']
      ring
    · simp only [AlgHom.comp_apply, theta_auxVar, qshift_auxVar, addLetter_auxVar]
  exact congrArg (fun f : Total L →ₐ[L] Total L => f F) key

end HJO.Sweep
