/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitCornerShift
public meta import HJO.Attr

/-! # The unit shift where it lives: the `y`-inverted total space

`HJO.Sweep.nsShiftExt` extends the unit shift `ϑ` of `HJO.Sweep.unitShiftTotal` to
`τ_kF = ϑ_k(F)∏_{i≤k}(1-y_i^{-1})`, and this map does **not** act on the completion of
`HJO.Sweep.pieceHat`: `ϑ` lowers degree, so on an infinite series it would produce an infinite sum
in each degree. Its home is the localization of the *polynomial* ring at the auxiliary variables,
and this file is that home, together with the second of the two relations Mellit records for
`d^*_+`, `HJO.Sweep.fracDplusStar_nsShiftExt`.

## Why the fraction field, and why that is not a weakening

The domain is `V_k[(y_1⋯y_k)^{-1}]`. Realised here as `HJO.Sweep.TotalFrac`, the fraction field of
the total space — a *larger* ring, into which every one of those localizations embeds,
`HJO.Sweep.Total` being a domain. This is the same move the library already makes at
`HJO.Sweep.qshift`, which is defined on the whole total space with the `τ_{k,i}` its restriction to
`V_k`: one ambient, and the per-`k` object a subring of it. Nothing is weakened — the formula is
Mellit's, and the statement below quantifies over more elements than Mellit's does, not fewer.

What the fraction field buys is that `y_i^{-1}` is an ordinary inverse rather than a
`IsLocalization.mk'`, so `∏_{i≤k}(1-y_i^{-1})` is written as it is written on paper.

## Where `u ≠ 0` comes from, and why it is not a new hypothesis

`d^*_+` extends to the fraction field only because it is injective, and `cy_{k+1}` is injective
only for `u ≠ 0` — at `u = 0` the corner letter `y_{k+1}` goes to `0`. That hypothesis is
implicit in the description of `cy_{k+1}` as the "`Λ`-algebra **automorphism** of `V_{k+1}`
with `cy_{k+1}(y_{k+1}) = uy_1`", which is false at `u = 0`. `HJO.Sweep.cycleShift` is only a
homomorphism; `HJO.Sweep.cycleShiftInv` and `HJO.Sweep.cycleShift_injective` below supply the
automorphism half, and `u ≠ 0` is exactly its cost.

## The three inverses this needs

A map extends to the fraction field exactly when it is injective, so this file first inverts the
three substitutions:

* `HJO.Sweep.unitShiftNegTotal` — `p_r ↦ p_r - 1`, inverse to `ϑ`;
* `HJO.Sweep.cycleShiftInv` — the cycle run backwards, inverse to `cy_{k+1}` **when `u ≠ 0`**,
  which is the one hypothesis the extension costs;
* and `HJO.Sweep.qshiftNeg`, already proved to be the inverse of `τ_{k,i}`
  (`HJO.Sweep.qshiftNeg_qshift`).

## Main results

* `HJO.Sweep.fracDplusStar_nsShiftExt`,
  `(1-y_1^{-1})d^*_+(τ_kF) = τ_{k+1}(d^*_+F)`.
* `HJO.Sweep.unitShiftTotal_cycleShift` — `ϑ` commutes with `cy_{k+1}`, the commutation the proof
  needs for the first factor.

## References

A. Mellit, *Toric braids and `(m,n)`-parking functions*, §3.7, for `HJO.Sweep.nsShiftExt` and
`HJO.Sweep.fracDplusStar_nsShiftExt`.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Sweep

section Inverses

variable {L : Type*} [Field L]

/-! ### Undoing the unit shift -/

/-- **The removal of the single letter `1`**: the `𝕜[y]`-algebra endomorphism of the total space
with `p_r ↦ p_r - 1`. It is the inverse of `HJO.Sweep.unitShiftTotal`, and the total-space form of
`HJO.Sym.unitShiftNeg`. -/
noncomputable def unitShiftNegTotal (L : Type*) [Field L] : Total L →ₐ[L] Total L :=
  MvPolynomial.aevalTower
    (MvPolynomial.aeval fun j : ℕ => (MvPolynomial.C (MvPolynomial.X j) - 1 : Total L))
    MvPolynomial.X

@[simp]
theorem unitShiftNegTotal_X (j : ℕ) :
    unitShiftNegTotal L (MvPolynomial.X j : Total L) = MvPolynomial.X j := by
  simp [unitShiftNegTotal]

theorem unitShiftNegTotal_powerSum (r : ℕ) :
    unitShiftNegTotal L (MvPolynomial.C (Sym.powerSum L (r + 1)))
      = MvPolynomial.C (Sym.powerSum L (r + 1)) - 1 := by
  simp [unitShiftNegTotal, Sym.powerSum]

theorem unitShiftNegTotal_unitShiftTotal (F : Total L) :
    unitShiftNegTotal L (unitShiftTotal L F) = F := by
  have key : (unitShiftNegTotal L).comp (unitShiftTotal L) = AlgHom.id L (Total L) := by
    refine MvPolynomial.algHom_ext' ?_ fun n => ?_
    · refine MvPolynomial.algHom_ext fun r => ?_
      have hC : (algebraMap (Sym.Lambda L) (Total L)) (MvPolynomial.X r)
          = MvPolynomial.C (Sym.powerSum L (r + 1)) := by
        simp [Sym.powerSum]
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hC, unitShiftTotal_powerSum,
        map_add, map_one, unitShiftNegTotal_powerSum, AlgHom.id_apply]
      ring
    · simp only [AlgHom.comp_apply, unitShiftTotal_X, unitShiftNegTotal_X, AlgHom.id_apply]
  exact congrArg (fun f : Total L →ₐ[L] Total L => f F) key

/-- **`ϑ` is injective**, off its inverse. -/
theorem unitShiftTotal_injective (L : Type*) [Field L] :
    Function.Injective (unitShiftTotal L : Total L →ₐ[L] Total L) := fun F G h => by
  rw [← unitShiftNegTotal_unitShiftTotal F, h, unitShiftNegTotal_unitShiftTotal]

/-! ### Undoing the cyclic shift -/

/-- **The cycle run backwards**: `y_{i+1} ↦ y_i` for `1 ≤ i ≤ k` and `y_1 ↦ u^{-1}y_{k+1}`. It is
the inverse of `HJO.Sweep.cycleShift` as soon as `u ≠ 0`. -/
noncomputable def cycleShiftInv (u : L) (k : ℕ) : Total L →ₐ[Sym.Lambda L] Total L :=
  MvPolynomial.aeval fun j : ℕ =>
    if j = 0 then scal u⁻¹ * MvPolynomial.X k
    else if j ≤ k then (MvPolynomial.X (j - 1) : Total L) else MvPolynomial.X j

theorem cycleShiftInv_cycleShift {u : L} (hu : u ≠ 0) (k : ℕ) (F : Total L) :
    cycleShiftInv u k (cycleShift u k F) = F := by
  have hsc : ∀ x : L, cycleShiftInv u k (scal x : Total L) = scal x := fun x =>
    AlgHom.commutes _ (MvPolynomial.C x)
  have key : (cycleShiftInv u k).comp (cycleShift u k) = AlgHom.id (Sym.Lambda L) (Total L) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    rw [AlgHom.comp_apply, cycleShift, MvPolynomial.aeval_X, AlgHom.id_apply]
    split_ifs with h1 h2
    · rw [cycleShiftInv, MvPolynomial.aeval_X]
      simp [show j + 1 ≤ k from by omega]
    · subst h2
      rw [map_mul, hsc, cycleShiftInv, MvPolynomial.aeval_X]
      simp only [ite_true]
      rw [← mul_assoc, ← scal_mul, mul_inv_cancel₀ hu, scal_one, one_mul]
    · rw [cycleShiftInv, MvPolynomial.aeval_X]
      simp [show j ≠ 0 from by omega, show ¬(j ≤ k) from by omega]
  exact congrArg (fun f : Total L →ₐ[Sym.Lambda L] Total L => f F) key

/-- **`cy_{k+1}` is injective for `u ≠ 0`.** At `u = 0` it is not: the corner letter `y_{k+1}` goes
to `0`. -/
theorem cycleShift_injective {u : L} (hu : u ≠ 0) (k : ℕ) :
    Function.Injective (cycleShift u k : Total L →ₐ[Sym.Lambda L] Total L) := fun F G h => by
  rw [← cycleShiftInv_cycleShift hu k F, h, cycleShiftInv_cycleShift hu k]

/-! ### The unit shift against the cyclic shift and the starred raising operator -/

/-- **`ϑ` commutes with `cy_{k+1}`.** Both are `𝕜`-algebra endomorphisms; `cy_{k+1}` fixes every
`p_r`, being `Λ`-linear, while `ϑ` adds the constant `1` to it, and `ϑ` fixes every auxiliary
variable while `cy_{k+1}` permutes them up to the scalar `u`, which `ϑ` also fixes. -/
theorem unitShiftTotal_cycleShift (u : L) (k : ℕ) (F : Total L) :
    unitShiftTotal L (cycleShift u k F) = cycleShift u k (unitShiftTotal L F) := by
  set A : Total L →ₐ[L] Total L := (cycleShift u k).restrictScalars L with hA
  have hAapp : ∀ G : Total L, A G = cycleShift u k G := fun _ => rfl
  have key : (unitShiftTotal L).comp A = A.comp (unitShiftTotal L) := by
    refine MvPolynomial.algHom_ext' ?_ fun n => ?_
    · refine MvPolynomial.algHom_ext fun r => ?_
      have hC : (algebraMap (Sym.Lambda L) (Total L)) (MvPolynomial.X r)
          = MvPolynomial.C (Sym.powerSum L (r + 1)) := by
        simp [Sym.powerSum]
      have hcyC : ∀ a : Sym.Lambda L, cycleShift u k (MvPolynomial.C a : Total L)
          = MvPolynomial.C a := fun a => AlgHom.commutes (cycleShift u k) a
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hC, hAapp, hcyC,
        unitShiftTotal_powerSum, map_add, map_one]
    · simp only [AlgHom.comp_apply, hAapp, unitShiftTotal_X]
      rw [cycleShift, MvPolynomial.aeval_X]
      split_ifs
      · rw [unitShiftTotal_X]
      · rw [map_mul, unitShiftTotal_scal, unitShiftTotal_X]
      · rw [unitShiftTotal_X]
  exact congrArg (fun f : Total L →ₐ[L] Total L => f F) key

/-- **`d^*_+` is injective for `u ≠ 0`**, being a composite of two injective substitutions. -/
theorem dplusStarAlg_injective (q : L) {u : L} (hu : u ≠ 0) (k : ℕ) :
    Function.Injective (dplusStarAlg q u k) :=
  (cycleShift_injective hu k).comp (qshift_injective q (k + 1))

/-- **`ϑ` commutes with `d^*_+`**, which is the first factor of the proof of
`HJO.Sweep.fracDplusStar_nsShiftExt`: `ϑ` commutes with `τ_{k+1,k+1}`
(`HJO.Sweep.unitShiftTotal_qshift`) and with `cy_{k+1}`. -/
theorem unitShiftTotal_dplusStarAlg (q u : L) (k : ℕ) (F : Total L) :
    unitShiftTotal L (dplusStarAlg q u k F) = dplusStarAlg q u k (unitShiftTotal L F) := by
  rw [dplusStarAlg_apply, dplusStarAlg_apply, unitShiftTotal_cycleShift, unitShiftTotal_qshift]

/-- **`d^*_+` advances an auxiliary variable**, `y_i ↦ y_{i+1}` for `1 ≤ i ≤ k`: `τ_{k+1,k+1}`
fixes it and `cy_{k+1}` shifts it. The corner value `cy_{k+1}(y_{k+1}) = uy_1` is never reached
below, which is what makes the second factor of `HJO.Sweep.fracDplusStar_nsShiftExt` a clean
reindexing. -/
theorem dplusStarAlg_auxVar (q u : L) {i k : ℕ} (h1 : 1 ≤ i) (hk : i ≤ k) :
    dplusStarAlg q u k (auxVar i : Total L) = auxVar (i + 1) := by
  rw [dplusStarAlg_apply, qshift_auxVar_apply, cycleShift_auxVar u h1 hk]

end Inverses

/-! ### The `y`-inverted total space -/

section Frac

variable {L : Type*} [Field L]

/-- **The total space with the auxiliary variables inverted.** `V_k[(y_1⋯y_k)^{-1}]` is a subring of
this field, and the maps below restrict to the on it; see the module docstring. -/
abbrev TotalFrac (L : Type*) [Field L] : Type _ := FractionRing (Total L)

/-- The image of a polynomial in the `y`-inverted total space. -/
noncomputable abbrev toFrac (F : Total L) : TotalFrac L := algebraMap (Total L) (TotalFrac L) F

theorem toFrac_injective (L : Type*) [Field L] : Function.Injective (toFrac (L := L)) :=
  IsFractionRing.injective (Total L) (TotalFrac L)

/-- **The extension of an injective substitution to the `y`-inverted total space.** A substitution
extends to the fraction field exactly when it is injective, and then in exactly one way. -/
noncomputable def fracLift {D : Total L →ₐ[L] Total L} (hD : Function.Injective D) :
    TotalFrac L →+* TotalFrac L :=
  IsFractionRing.lift (A := Total L) (K := TotalFrac L)
    (g := (algebraMap (Total L) (TotalFrac L)).comp D.toRingHom)
    ((IsFractionRing.injective (Total L) (TotalFrac L)).comp hD)

theorem fracLift_toFrac {D : Total L →ₐ[L] Total L} (hD : Function.Injective D) (F : Total L) :
    fracLift hD (toFrac F) = toFrac (D F) := by
  rw [fracLift, IsFractionRing.lift_algebraMap]
  rfl

/-- **`ϑ` on the `y`-inverted total space.** -/
noncomputable def fracUnitShift (L : Type*) [Field L] : TotalFrac L →+* TotalFrac L :=
  fracLift (unitShiftTotal_injective L)

/-- **`d^*_+` on the `y`-inverted total space.** -/
noncomputable def fracDplusStar (q : L) {u : L} (hu : u ≠ 0) (k : ℕ) :
    TotalFrac L →+* TotalFrac L :=
  fracLift (dplusStarAlg_injective q hu k)

theorem fracUnitShift_toFrac (F : Total L) :
    fracUnitShift L (toFrac F) = toFrac (unitShiftTotal L F) :=
  fracLift_toFrac _ F

theorem fracDplusStar_toFrac (q : L) {u : L} (hu : u ≠ 0) (k : ℕ) (F : Total L) :
    fracDplusStar q hu k (toFrac F) = toFrac (dplusStarAlg q u k F) :=
  fracLift_toFrac _ F

/-- The auxiliary variable `y_i`, read in the `y`-inverted total space; it is nonzero, so it has an
inverse there. -/
noncomputable abbrev auxFrac (L : Type*) [Field L] (i : ℕ) : TotalFrac L := toFrac (auxVar i)

theorem auxFrac_ne_zero (L : Type*) [Field L] (i : ℕ) : auxFrac L i ≠ 0 := fun hz =>
  MvPolynomial.X_ne_zero (R := Sym.Lambda L) (i - 1)
    ((map_eq_zero_iff (algebraMap (Total L) (TotalFrac L))
      (IsFractionRing.injective (Total L) (TotalFrac L))).1 hz)

/-- **The extended unit alphabet shift `τ_k`.** `HJO.Sweep.nsShiftExt`:
`τ_kF = ϑ_k(F)∏_{i=1}^{k}(1-y_i^{-1})`.

Mellit reads it on `V_k[(y_1⋯y_k)^{-1}]`; here the domain is the whole `y`-inverted total space, of
which that localization is a subring, so this is the one map whose restriction is Mellit's — the
convention `HJO.Sweep.qshift` already follows for `τ_{k,i}`. Mellit restricts further, to
`y_1⋯y_kV_k`, which is where the same formula stays polynomial; the restriction is unnecessary, and
`HJO.Sweep.fracDplusStar_nsShiftExt` has to be read off it in any case, since at `k = 0` both sides
already leave `V_1`. -/
@[hjo "def_mellit_ns_shift_ext"]
noncomputable def nsShiftExt (L : Type*) [Field L] (k : ℕ) (F : TotalFrac L) : TotalFrac L :=
  fracUnitShift L F * ∏ i ∈ range k, (1 - (auxFrac L (i + 1))⁻¹)

theorem nsShiftExt_apply (k : ℕ) (F : TotalFrac L) :
    nsShiftExt L k F = fracUnitShift L F * ∏ i ∈ range k, (1 - (auxFrac L (i + 1))⁻¹) := rfl

/-- **The starred raising operator against the unit shift.** `HJO.Sweep.fracDplusStar_nsShiftExt`:
`(1-y_1^{-1})d^*_+(τ_kF) = τ_{k+1}(d^*_+F)`.

The hypothesis `u ≠ 0` is the word "automorphism" in the description of `cy_{k+1}`, made explicit:
it is what lets `d^*_+` be read on the `y`-inverted total space at all. On Mellit's
`V_k[(y_1⋯y_k)^{-1}]`, which inverts `y_1, …, y_k` and not `y_{k+1}`, the corner value `uy_1` is
never inverted and the hypothesis would not appear; it is the price of the single ambient.

Two facts, exactly as Mellit runs it. `d^*_+` commutes with `ϑ`
(`HJO.Sweep.unitShiftTotal_dplusStarAlg`), which handles the first factor; and `d^*_+` sends `y_i`
to `y_{i+1}` for `1 ≤ i ≤ k` (`HJO.Sweep.dplusStarAlg_auxVar`), the corner value `uy_1` never being
reached, so the product `∏_{i≤k}(1-y_i^{-1})` goes to `∏_{2≤i≤k+1}(1-y_i^{-1})` — and multiplying
by `1-y_1^{-1}` completes it to the product at `k+1`. -/
@[hjo "lem_mellit_ns_dstar_shift"]
theorem fracDplusStar_nsShiftExt (q : L) {u : L} (hu : u ≠ 0) (k : ℕ) (F : TotalFrac L) :
    (1 - (auxFrac L 1)⁻¹) * fracDplusStar q hu k (nsShiftExt L k F)
      = nsShiftExt L (k + 1) (fracDplusStar q hu k F) := by
  have hcomm : (fracDplusStar q hu k).comp (fracUnitShift L)
      = (fracUnitShift L).comp (fracDplusStar q hu k) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (Total L)) ?_
    refine RingHom.ext fun G => ?_
    simp only [RingHom.comp_apply]
    change fracDplusStar q hu k (fracUnitShift L (toFrac G))
      = fracUnitShift L (fracDplusStar q hu k (toFrac G))
    rw [fracUnitShift_toFrac, fracDplusStar_toFrac, fracDplusStar_toFrac, fracUnitShift_toFrac,
      unitShiftTotal_dplusStarAlg]
  have hprod : fracDplusStar q hu k (∏ i ∈ range k, (1 - (auxFrac L (i + 1))⁻¹))
      = ∏ i ∈ range k, (1 - (auxFrac L (i + 2))⁻¹) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [map_sub, map_one, map_inv₀, fracDplusStar_toFrac,
      dplusStarAlg_auxVar q u (by omega) (show i + 1 ≤ k from by omega)]
  have hcommG : ∀ G : TotalFrac L,
      fracDplusStar q hu k (fracUnitShift L G) = fracUnitShift L (fracDplusStar q hu k G) :=
    fun G => congrArg (fun f : TotalFrac L →+* TotalFrac L => f G) hcomm
  rw [nsShiftExt_apply, nsShiftExt_apply, map_mul, hcommG, hprod, Finset.prod_range_succ']
  ring

end Frac

end HJO.Sweep

end
