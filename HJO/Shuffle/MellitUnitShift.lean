/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Symmetric.SymmetricFunctions
public meta import HJO.Attr

/-! # The unit alphabet shift `τ`

Mellit's normalisation of the sweep uses the substitution `τ(f) = f[X + 1]`, the addition of the
single letter `1` to the alphabet. On the power sums it is `p_r ↦ p_r + 1`, since a single letter
`1` contributes `1 ^ r = 1` to every power sum, and that is what is defined here.

## Main definitions

* `HJO.Sym.unitShift`: `τ`, the substitution `f ↦ f[X + 1]`.
* `HJO.Sym.unitShiftNeg`: `f ↦ f[X - 1]`, the removal of the same letter.
* `HJO.Sym.unitShiftEquiv`: `τ` as an algebra automorphism of `Λ`, with `unitShiftNeg` its inverse.

## Main results

* `HJO.Sym.unitShift_powerSum`, `HJO.Sym.unitShiftNeg_powerSum`: the action on the power sums,
  `p_r ↦ p_r ± 1` for `r ≥ 1`. This is the value check against the formula: the index
  shift of `HJO.Sym.powerSum` is what the definition below has to get right.
* `HJO.Sym.unitShiftNeg_unitShift`, `HJO.Sym.unitShift_unitShiftNeg`: adding and then removing the
  letter `1` is the identity, in either order. Hence `τ` is bijective, which is the first half of
  `HJO.Sym.nsShiftComp_injective`.

## Implementation notes

`τ` is an **algebra** endomorphism, not merely a `𝕜`-linear map: a plethystic substitution of an
alphabet is multiplicative, and the stronger type is what every use of it needs. Stating it as
`MvPolynomial.aeval` of the prescription on the generators is the same construction the library's
other displacements use (`HJO.Sym.plethShift`, `HJO.Sym.plethCreate`), so nothing new is introduced.

The base is an arbitrary commutative ring: `τ` reads no parameter and no inverse, so there is no
reason to state it over the standing field. Generator `i` of `Lambda K` is `p_{i+1}`, so the
prescription is `X i ↦ X i + 1`; the truncated index of `HJO.Sym.powerSum` means
`unitShift_powerSum` needs `1 ≤ r`, and at `r = 0` the statement would be about `p_1` under another
name.

The conjugate shift `τ*` of `HJO.Sym.nsShiftStar` is **not** here: its target is the
completion `Λ̂`, a different ambient ring, and it belongs with the completion.

## References

The definition `HJO.Sym.unitShift`, using `HJO.Sym.Lambda` and `HJO.Sym.plethShift`. Transcribing A.
Mellit, *Toric braids and `(m, n)`-parking functions*, §6. Used by
`HJO.Sym.nsShiftComp_injective` and the normalisation of the sweep's right-hand side.
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K]

/-- **The unit alphabet shift `τ`**: the substitution `f ↦ f[X + 1]`, the addition of the single
letter `1` to the alphabet. A single letter `1` contributes `1 ^ r = 1` to the power sum `p_r`, so
`τ` is the algebra endomorphism of `Λ` with `p_r ↦ p_r + 1` for every `r ≥ 1`
(`HJO.Sym.unitShift_powerSum`). It is bijective, `HJO.Sym.unitShiftNeg` being its inverse. -/
@[hjo "def_mellit_ns_shift"]
noncomputable def unitShift : Lambda K →ₐ[K] Lambda K :=
  MvPolynomial.aeval fun i => MvPolynomial.X i + 1

/-- The removal of the single letter `1`: the substitution `f ↦ f[X - 1]`, the algebra endomorphism
of `Λ` with `p_r ↦ p_r - 1`. It is the inverse of `HJO.Sym.unitShift`. -/
noncomputable def unitShiftNeg : Lambda K →ₐ[K] Lambda K :=
  MvPolynomial.aeval fun i => MvPolynomial.X i - 1

/-- **`τ(p_r) = p_r + 1` for `r ≥ 1`**: the formula, read against the index convention
of `HJO.Sym.powerSum`, under which generator `i` is `p_{i+1}`. -/
theorem unitShift_powerSum {r : ℕ} (hr : 1 ≤ r) :
    unitShift (powerSum K r) = powerSum K r + 1 := by
  obtain ⟨i, rfl⟩ : ∃ i, r = i + 1 := ⟨r - 1, by omega⟩
  rw [powerSum, unitShift, Nat.add_sub_cancel, MvPolynomial.aeval_X]

/-- `f[X - 1]` sends `p_r` to `p_r - 1`, for `r ≥ 1`. -/
theorem unitShiftNeg_powerSum {r : ℕ} (hr : 1 ≤ r) :
    unitShiftNeg (powerSum K r) = powerSum K r - 1 := by
  obtain ⟨i, rfl⟩ : ∃ i, r = i + 1 := ⟨r - 1, by omega⟩
  rw [powerSum, unitShiftNeg, Nat.add_sub_cancel, MvPolynomial.aeval_X]

/-- Removing the letter `1` after adding it is the identity, as algebra maps. -/
theorem unitShiftNeg_comp_unitShift :
    (unitShiftNeg : Lambda K →ₐ[K] Lambda K).comp unitShift = AlgHom.id K (Lambda K) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  simp [unitShift, unitShiftNeg]

/-- Adding the letter `1` after removing it is the identity, as algebra maps. -/
theorem unitShift_comp_unitShiftNeg :
    (unitShift : Lambda K →ₐ[K] Lambda K).comp unitShiftNeg = AlgHom.id K (Lambda K) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  simp [unitShift, unitShiftNeg]

/-- Removing the letter `1` after adding it is the identity. -/
@[simp]
theorem unitShiftNeg_unitShift (f : Lambda K) : unitShiftNeg (unitShift f) = f :=
  congrArg (fun g : Lambda K →ₐ[K] Lambda K => g f) unitShiftNeg_comp_unitShift

/-- Adding the letter `1` after removing it is the identity. -/
@[simp]
theorem unitShift_unitShiftNeg (f : Lambda K) : unitShift (unitShiftNeg f) = f :=
  congrArg (fun g : Lambda K →ₐ[K] Lambda K => g f) unitShift_comp_unitShiftNeg

/-- `τ` as an algebra automorphism of `Λ`. Its bijectivity is the first half of
`HJO.Sym.nsShiftComp_injective`: adding and then subtracting the single letter `1` is the identity
on each power sum. -/
noncomputable def unitShiftEquiv : Lambda K ≃ₐ[K] Lambda K :=
  AlgEquiv.ofAlgHom unitShift unitShiftNeg unitShift_comp_unitShiftNeg unitShiftNeg_comp_unitShift

@[simp]
theorem unitShiftEquiv_apply (f : Lambda K) : unitShiftEquiv f = unitShift f := rfl

/-- `τ` is injective. -/
theorem unitShift_injective : Function.Injective (unitShift : Lambda K →ₐ[K] Lambda K) :=
  fun _ _ h => by
    simpa using congrArg (unitShiftNeg : Lambda K →ₐ[K] Lambda K) h

/-- Value check at a product: `τ(p_1 p_2) = (p_1 + 1)(p_2 + 1)`, so the shift really is
multiplicative and not the linear extension of `p_r ↦ p_r + 1` on the power-sum monomials. -/
theorem unitShift_powerSum_mul_powerSum :
    unitShift (powerSum K 1 * powerSum K 2) = (powerSum K 1 + 1) * (powerSum K 2 + 1) := by
  rw [map_mul, unitShift_powerSum le_rfl, unitShift_powerSum (by omega)]

end HJO.Sym
