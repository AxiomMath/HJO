/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.SweepCM
public import HJO.Shuffle.CMRaising
public import HJO.Shuffle.MellitShiftDop
public meta import HJO.Attr

/-! # Inverting the letter substitution, and the unit shift against the lowering operators

Two results of the sweep's operator layer, both of which turn on the *virtual* reading of the
letters that `HJO.Sweep.qshift` and `HJO.Sweep.unitShiftTotal` add.

`HJO.Sweep.qshiftNeg_qshift` says `τ^-_{k,i}` undoes `τ_{k,i}`. On the total space this is an
identity of `𝕜`-algebra endomorphisms of `MvPolynomial ℕ Λ`, so `MvPolynomial.algHom_ext'` reduces
it to the auxiliary variables — fixed by both — and to the power sums, where the two added letters
cancel term by term. The composite in the other order is the same computation and is proved as well,
so the two substitutions are mutually inverse automorphisms and neither is merely a left inverse.

`HJO.Sweep.unitShiftTotal_dminusCM` compares the unit shift `ϑ` with Carlsson and Mellit's own
lowering operator `d_-` of `HJO.Sweep.dminusCM` and with the modified operator `d^♭_-` of
`HJO.Sweep.dminus`: `ϑ d_- = d_-ϑ + d^♭_-ϑ`. Both operators are a coefficient extraction after
`τ^-_{k,k}`, and `ϑ` commutes with `τ^-_{k,k}`, so the whole content is the behaviour of the
extraction — which is the identity `e_n[X+1] = e_n[X] + e_{n-1}[X]`, already proved as
`HJO.Sym.unitShift_elemSymm`, transported through `HJO.Sweep.lowerCoeffShift`. The `+ d^♭_-ϑ` term
is exactly the `e_{n-1}` half.

## Main results

* `HJO.Sweep.qshiftNeg_qshift` and its mirror image `HJO.Sweep.qshift_qshiftNeg`.
* `HJO.Sweep.unitShiftTotal_qshiftNeg` — `ϑ` commutes with `τ^-_{k,i}`, the total-space form of the
  commutation the proof of `HJO.Sweep.unitShiftTotal_dminusCM` opens with. (Its companion for
  `τ_{k,i}`, is `HJO.Sweep.unitShiftTotal_qshift`.)
* `HJO.Sweep.unitShiftTotal_lowerCoeffShift` — the coefficient extraction against `ϑ`, which is the
  identity `e_n[X+1] = e_n[X] + e_{n-1}[X]` read on every `y`-monomial at once.
* `HJO.Sweep.unitShiftTotal_dminusCM`.

## Implementation notes

Both results are naturally stated on `V_k`, with `1 ≤ i ≤ k` and `k ≥ 1`. Here they are stated on
the total space `HJO.Sweep.Total`, where the index of the substitution is unrestricted and no width
hypothesis appears: each operator is the one endomorphism of the total space whose restriction to
`V_k` is the operator on `V_k`, so the statements below specialise to `V_k` at every `k`.

`HJO.Sweep.unitShiftTotal_dminusCM`'s proof runs over the `y`-monomials rather than over "the
expansion `τ^-_{k,k}(F) = ∑_j F_j y_k^j`". That expansion is what `HJO.Sweep.lowerCoeff` and
`HJO.Sweep.lowerCoeffShift` already are — the extraction is defined on the `Λ`-basis of
`y`-monomials — so `MvPolynomial.induction_on'` over that basis is the sum `∑_j`, with
the `Λ`-coefficient of each monomial the `F_j`.

## References

The raising and lowering operators: `HJO.Sweep.qshiftNeg_qshift`; the modified lowering operator:
`HJO.Sweep.unitShiftTotal`, `HJO.Sweep.unitShiftTotal_dminusCM`. Transcribing A. Mellit, *Toric
braids and `(m,n)`-parking functions*, §3.2.
-/

@[expose] public section

namespace HJO.Sweep

open MvPolynomial

section Field

variable {L : Type*} [Field L]

/-! ### The two letter substitutions are inverse -/

/-- `τ^-_{k,m}` fixes a scalar of `𝕜`, being an `𝕜`-algebra map. -/
@[simp]
theorem qshiftNeg_scal (q : L) (m : ℕ) (x : L) : qshiftNeg q m (scal x : Total L) = scal x := by
  rw [scal_eq_algebraMap, AlgHom.commutes]

/-- `τ^-_{k,m}` fixes every auxiliary variable, being a `𝕜[y]`-algebra map. -/
@[simp]
theorem qshiftNeg_auxVar_apply (q : L) (m j : ℕ) :
    qshiftNeg q m (auxVar j : Total L) = auxVar j :=
  qshiftNeg_auxVar q m (j - 1)

/-- **The two letter substitutions are inverse.** `HJO.Sweep.qshiftNeg_qshift`:
`τ^-_{k,i}(τ_{k,i}(F)) = F`.

Both composites are `𝕜`-algebra endomorphisms of `Total L = MvPolynomial ℕ Λ`, so
`MvPolynomial.algHom_ext'` reduces the claim to the auxiliary variables, which both substitutions
fix, and to the power sums, where one adds `(q^r-1)y_i^r` and the other subtracts it. -/
@[hjo "lem_cm_qshift_inverse"]
theorem qshiftNeg_qshift (q : L) (i : ℕ) (F : Total L) : qshiftNeg q i (qshift q i F) = F := by
  have key : (qshiftNeg q i).comp (qshift q i) = AlgHom.id L (Total L) := by
    refine MvPolynomial.algHom_ext' ?_ fun n => ?_
    · refine MvPolynomial.algHom_ext fun r => ?_
      have hC : (algebraMap (Sym.Lambda L) (Total L)) (MvPolynomial.X r)
          = MvPolynomial.C (Sym.powerSum L (r + 1)) := by
        simp [Sym.powerSum]
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hC, qshift_powerSum, map_add,
        map_mul, map_pow, qshiftNeg_powerSum, qshiftNeg_scal, qshiftNeg_auxVar_apply,
        AlgHom.id_apply]
      ring
    · simp only [AlgHom.comp_apply, qshift_auxVar, qshiftNeg_auxVar, AlgHom.id_apply]
  exact congrArg (fun f : Total L →ₐ[L] Total L => f F) key

/-- **The same composite the other way round**, `τ_{k,i}(τ^-_{k,i}(F)) = F`. Together with
`HJO.Sweep.qshiftNeg_qshift` this makes each substitution an automorphism of the total space, which
is more than a one-sided inverse and is what a statement reading `τ_{k,i}` as invertible
needs. -/
theorem qshift_qshiftNeg (q : L) (i : ℕ) (F : Total L) : qshift q i (qshiftNeg q i F) = F := by
  have key : (qshift q i).comp (qshiftNeg q i) = AlgHom.id L (Total L) := by
    refine MvPolynomial.algHom_ext' ?_ fun n => ?_
    · refine MvPolynomial.algHom_ext fun r => ?_
      have hC : (algebraMap (Sym.Lambda L) (Total L)) (MvPolynomial.X r)
          = MvPolynomial.C (Sym.powerSum L (r + 1)) := by
        simp [Sym.powerSum]
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hC, qshiftNeg_powerSum, map_sub,
        map_mul, map_pow, qshift_powerSum, qshift_scal, qshift_auxVar_apply, AlgHom.id_apply]
      ring
    · simp only [AlgHom.comp_apply, qshift_auxVar, qshiftNeg_auxVar, AlgHom.id_apply]
  exact congrArg (fun f : Total L →ₐ[L] Total L => f F) key

/-- **`τ_{k,i}` is injective**, off the inverse above. -/
theorem qshift_injective (q : L) (i : ℕ) :
    Function.Injective (qshift q i : Total L →ₐ[L] Total L) := fun F G h => by
  rw [← qshiftNeg_qshift q i F, h, qshiftNeg_qshift]

/-- **`τ^-_{k,i}` is injective**, off the inverse above. -/
theorem qshiftNeg_injective (q : L) (i : ℕ) :
    Function.Injective (qshiftNeg q i : Total L →ₐ[L] Total L) := fun F G h => by
  rw [← qshift_qshiftNeg q i F, h, qshift_qshiftNeg]

/-! ### The unit shift against the two letter substitutions -/

/-- **`ϑ` commutes with `τ_{k,i}`**, `HJO.Sweep.unitShiftTotal_qshift`. Both composites
send `p_r` to `p_r + 1 + (q^r-1)y_i^r` and fix every auxiliary variable. -/
@[hjo "lem_vmod_tau_qshift_commute"]
theorem unitShiftTotal_qshift (q : L) (i : ℕ) (F : Total L) :
    unitShiftTotal L (qshift q i F) = qshift q i (unitShiftTotal L F) := by
  have key : (unitShiftTotal L).comp (qshift q i) = (qshift q i).comp (unitShiftTotal L) := by
    refine MvPolynomial.algHom_ext' ?_ fun n => ?_
    · refine MvPolynomial.algHom_ext fun r => ?_
      have hC : (algebraMap (Sym.Lambda L) (Total L)) (MvPolynomial.X r)
          = MvPolynomial.C (Sym.powerSum L (r + 1)) := by
        simp [Sym.powerSum]
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hC, qshift_powerSum,
        unitShiftTotal_powerSum, map_add, map_mul, map_pow, map_one, unitShiftTotal_scal,
        unitShiftTotal_auxVar]
      ring
    · simp only [AlgHom.comp_apply, unitShiftTotal_X, qshift_auxVar]
  exact congrArg (fun f : Total L →ₐ[L] Total L => f F) key

/-- **`ϑ` commutes with `τ^-_{k,i}`**, the same computation with the added letter negated. This is
the commutation the proof of `HJO.Sweep.unitShiftTotal_dminusCM` opens with. -/
theorem unitShiftTotal_qshiftNeg (q : L) (i : ℕ) (F : Total L) :
    unitShiftTotal L (qshiftNeg q i F) = qshiftNeg q i (unitShiftTotal L F) := by
  have key : (unitShiftTotal L).comp (qshiftNeg q i)
      = (qshiftNeg q i).comp (unitShiftTotal L) := by
    refine MvPolynomial.algHom_ext' ?_ fun n => ?_
    · refine MvPolynomial.algHom_ext fun r => ?_
      have hC : (algebraMap (Sym.Lambda L) (Total L)) (MvPolynomial.X r)
          = MvPolynomial.C (Sym.powerSum L (r + 1)) := by
        simp [Sym.powerSum]
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hC, qshiftNeg_powerSum,
        unitShiftTotal_powerSum, map_sub, map_add, map_mul, map_pow, map_one, unitShiftTotal_scal,
        unitShiftTotal_auxVar]
      ring
    · simp only [AlgHom.comp_apply, unitShiftTotal_X, qshiftNeg_auxVar]
  exact congrArg (fun f : Total L →ₐ[L] Total L => f F) key

/-! ### The unit shift on the coefficient ring and on the monomials -/

/-- **`ϑ` acts on the `Λ`-coefficients as `HJO.Sym.unitShift`.** Both sides are `𝕜`-algebra maps
`Λ → Total L` sending the generator `p_{r+1}` to `p_{r+1} + 1`. -/
theorem unitShiftTotal_C (a : Sym.Lambda L) :
    unitShiftTotal L (MvPolynomial.C a) = MvPolynomial.C (Sym.unitShift a) := by
  have key : (unitShiftTotal L).comp (IsScalarTower.toAlgHom L (Sym.Lambda L) (Total L))
      = (IsScalarTower.toAlgHom L (Sym.Lambda L) (Total L)).comp Sym.unitShift := by
    refine MvPolynomial.algHom_ext fun r => ?_
    simp [unitShiftTotal, Sym.unitShift]
  simpa using congrArg (fun f : Sym.Lambda L →ₐ[L] Total L => f a) key

/-- **`ϑ` on a `y`-monomial** moves the `Λ`-coefficient and fixes the monomial, being a
`𝕜[y]`-algebra map. -/
theorem unitShiftTotal_monomial (d : ℕ →₀ ℕ) (a : Sym.Lambda L) :
    unitShiftTotal L (MvPolynomial.monomial d a) = MvPolynomial.monomial d (Sym.unitShift a) := by
  rw [MvPolynomial.monomial_eq, MvPolynomial.monomial_eq, map_mul, unitShiftTotal_C]
  congr 1
  rw [map_finsuppProd]
  exact Finsupp.prod_congr fun n _ => by rw [map_pow, unitShiftTotal_X]

end Field

section Rational

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- `HJO.Sweep.lowerCoeff` on a `y`-monomial with an arbitrary `Λ`-coefficient, the extraction being
`Λ`-linear. -/
theorem lowerCoeff_monomial' (j : ℕ) (d : ℕ →₀ ℕ) (a : Sym.Lambda L) :
    lowerCoeff L j (MvPolynomial.monomial d a)
      = MvPolynomial.C a * ((-1 : Total L) ^ d j * MvPolynomial.C (Sym.elemSymm L (d j)) *
        MvPolynomial.monomial (Finsupp.erase j d) 1) := by
  have h : (MvPolynomial.monomial d a : Total L) = a • MvPolynomial.monomial d 1 := by
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_mul_monomial, mul_one]
  rw [h, map_smul, lowerCoeff_monomial, MvPolynomial.smul_eq_C_mul]

/-- `HJO.Sweep.lowerCoeffShift` on a `y`-monomial with an arbitrary `Λ`-coefficient. -/
theorem lowerCoeffShift_monomial' (j : ℕ) (d : ℕ →₀ ℕ) (a : Sym.Lambda L) :
    lowerCoeffShift L j (MvPolynomial.monomial d a)
      = MvPolynomial.C a * ((-1 : Total L) ^ d j * MvPolynomial.C (Sym.elemSymm L (d j + 1)) *
        MvPolynomial.monomial (Finsupp.erase j d) 1) := by
  have h : (MvPolynomial.monomial d a : Total L) = a • MvPolynomial.monomial d 1 := by
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_mul_monomial, mul_one]
  rw [h, map_smul, lowerCoeffShift_monomial, MvPolynomial.smul_eq_C_mul]

/-- **The coefficient extraction of `d_-` against the unit shift.** On each `y`-monomial the
extraction contributes the single elementary function `e_{m+1}`, and `ϑ(e_{m+1}) = e_{m+1} + e_m`
by `HJO.Sym.unitShift_elemSymm`; the second summand is the same extraction with the index lowered,
which is `HJO.Sweep.lowerCoeff`. So the whole difference between the two sides is the identity
`e_n[X+1] = e_n[X] + e_{n-1}[X]`, read on every monomial at once.

The induction over the `y`-monomials is the expansion `τ^-_{k,k}(F) = ∑_j F_j y_k^j`:
the two extractions are defined on that basis, and the `Λ`-coefficient of a monomial is
`F_j`. -/
theorem unitShiftTotal_lowerCoeffShift (j : ℕ) (G : Total L) :
    unitShiftTotal L (lowerCoeffShift L j G)
      = lowerCoeffShift L j (unitShiftTotal L G) + lowerCoeff L j (unitShiftTotal L G) := by
  induction G using MvPolynomial.induction_on' with
  | monomial d a =>
    rw [lowerCoeffShift_monomial', unitShiftTotal_monomial, lowerCoeffShift_monomial',
      lowerCoeff_monomial', map_mul, map_mul, map_mul, unitShiftTotal_C, unitShiftTotal_C,
      map_pow, map_neg, map_one, Sym.unitShift_elemSymm]
    have hm : unitShiftTotal L (MvPolynomial.monomial (Finsupp.erase j d) (1 : Sym.Lambda L))
        = MvPolynomial.monomial (Finsupp.erase j d) (1 : Sym.Lambda L) := by
      rw [unitShiftTotal_monomial, map_one]
    rw [hm, MvPolynomial.C_add]
    ring
  | add p q hp hq => simp only [map_add, hp, hq]; ring

/-- **The unit shift and the lowering operators.** `HJO.Sweep.unitShiftTotal_dminusCM`:
`ϑ_{k-1}(d_-F) = d_-(ϑ_kF) + d^♭_-(ϑ_kF)`, with `d_-` the operator of `HJO.Sweep.dminusCM` and
`d^♭_-` the modified one of `HJO.Sweep.dminus`.

Both operators are `HJO.Sweep.lowerCoeffShift` resp. `HJO.Sweep.lowerCoeff` after `τ^-_{k,k}`, and
`ϑ` commutes with `τ^-_{k,k}` (`HJO.Sweep.unitShiftTotal_qshiftNeg`), so the statement is
`HJO.Sweep.unitShiftTotal_lowerCoeffShift` with that commutation in front of it.

On the total space `ϑ` does not depend on the width, so the `ϑ_{k-1}` on the left and
`ϑ_k` on the right are the same map; the `k ≥ 1` is not needed, the two operators being
defined at every index. -/
@[hjo "lem_vmod_tau_dminus"]
theorem unitShiftTotal_dminusCM (q : L) (k : ℕ) (F : Total L) :
    unitShiftTotal L (dminusCM q k F)
      = dminusCM q k (unitShiftTotal L F) + dminus q k (unitShiftTotal L F) := by
  rw [dminusCM, dminus]
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    LinearMap.restrictScalars_apply]
  rw [unitShiftTotal_lowerCoeffShift, unitShiftTotal_qshiftNeg]

end Rational

end HJO.Sweep

end
