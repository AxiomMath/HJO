/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepModule
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public meta import HJO.Attr

/-! # The graded piece of the sweep is the tensor product

`HJO.Sweep.piece L k` is the subalgebra of `HJO.Sweep.Total L = Λ[y_1, y_2, …]` of the elements
using only `y_1, …, y_k`; it is the graded piece `V_k` of the sweep. This file exhibits it as
`V_k = Λ ⊗_𝕜 𝕜[y_1, …, y_k]` on the nose: a `Λ`-algebra isomorphism onto `Λ ⊗[L] L[y_1, …, y_k]`,
the tensor product over the base ring of the library's own ring of symmetric functions with a
polynomial ring in exactly `k` variables.

Without it the definition of `V_k` would be a subalgebra that a reader has to be convinced is the
tensor product; with it the two are one object, so the operators of `HJO/Shuffle/SweepModule.lean`
act on the module and not on a weaker relative of it.

## Main definitions

* `HJO.Sweep.pieceTensorAlgEquiv`: the `Λ`-algebra isomorphism
  `piece L k ≃ₐ[Λ] Λ ⊗[L] L[y_1, …, y_k]`.

## Implementation notes

The isomorphism is the composite of three Mathlib equivalences: `MvPolynomial.supported` on
`Set.Iio k` is a polynomial ring on that subtype (`MvPolynomial.supportedEquivMvPolynomial`), the
subtype is `Fin k` (`HJO.Sweep.setIioEquivFin`), and a polynomial ring over `Λ` is the base change
of a polynomial ring over `L` (`MvPolynomial.algebraTensorAlgEquiv`). The middle step is the only
place the *number* of auxiliary variables enters, and it is what makes the count `k` rather than
"some finite set".

`setIioEquivFin` is stated for `Set.Iio k` in `ℕ` rather than taken from Mathlib's
`Finset.orderIsoOfFin` family, because the index set of `piece` is a `Set` and the coercion
`↥(Set.Iio k) → ℕ` is already the bound: both directions are `rfl`.

## References

The definition `HJO.Sweep.piece` of the sweep process, using `HJO.Sym.Lambda`.
-/

@[expose] public section

open MvPolynomial TensorProduct

namespace HJO.Sweep

/-- The subtype of naturals below `k` is `Fin k`. Both directions are the identity on the
underlying natural number, so both round trips are `rfl`. -/
def setIioEquivFin (k : ℕ) : (Set.Iio k : Set ℕ) ≃ Fin k where
  toFun i := ⟨i.1, i.2⟩
  invFun i := ⟨(i : ℕ), i.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem setIioEquivFin_apply {k : ℕ} (i : (Set.Iio k : Set ℕ)) :
    ((setIioEquivFin k i : Fin k) : ℕ) = (i : ℕ) := rfl

@[simp]
theorem setIioEquivFin_symm_apply {k : ℕ} (i : Fin k) :
    (((setIioEquivFin k).symm i : (Set.Iio k : Set ℕ)) : ℕ) = (i : ℕ) := rfl

variable (L : Type*) [CommRing L]

/-- **The graded piece is the tensor product.** `V_k = Λ ⊗_𝕜 𝕜[y_1, …, y_k]` of
`HJO.Sweep.piece`, read in the total space of the sweep: `HJO.Sweep.piece L k` is isomorphic as a
`Λ`-algebra to `Λ ⊗[L] L[y_1, …, y_k]`, the tensor product over the base ring of the library's
own ring of symmetric functions with the polynomial ring in exactly `k` auxiliary variables.

The first factor is `HJO.Sym.Lambda L`, reused and not redeclared; the second is
`MvPolynomial (Fin k) L`, whose variables are the `y_1, …, y_k` under the index shift
of `HJO.Sweep.auxVar`; and the tensor product is over `L`, the `𝕜`. -/
noncomputable def pieceTensorAlgEquiv (k : ℕ) :
    piece L k ≃ₐ[Sym.Lambda L] (Sym.Lambda L) ⊗[L] MvPolynomial (Fin k) L :=
  (MvPolynomial.supportedEquivMvPolynomial (R := Sym.Lambda L) (Set.Iio k)).trans
    ((MvPolynomial.renameEquiv (Sym.Lambda L) (setIioEquivFin k)).trans
      (MvPolynomial.algebraTensorAlgEquiv L (Sym.Lambda L)).symm)

end HJO.Sweep
