/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Symmetric.SymmetricFunctions
public meta import HJO.Attr

/-! # The axis substitution

The one object of the symmetric-function machinery not already carried by
`HJO.Symmetric.SymmetricFunctions`: the axis substitution `Υ`, the `L`-algebra endomorphism of
`Lambda L` sending the formal power sum `p_k` to the axis generator `U_k` for every `k ≥ 1`.

Since `Lambda L` is the polynomial algebra over `L` on the generators `p_1, p_2, …` -- generator
`i` of `MvPolynomial ℕ L` standing for `p_{i+1}` -- prescribing the images of the `p_k` freely
determines an `L`-algebra endomorphism, and `MvPolynomial.aeval` is that prescription. The natural
subtraction in `Sym.powerSum` makes `powerSum L 0` the same generator as `powerSum L 1`, so the
characterisation `Sym.axisSub_powerSum` carries the hypothesis `k ≥ 1`; the form on the generators
themselves, with no hypothesis, is `Sym.axisSub_X`.

The parameter `v` is to be read as `q * u`, as in `Sym.axisGen` and `Sym.IsSlopeHom`.
-/

@[expose] public section

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- The axis substitution `Υ` at the parameter `v`: the `L`-algebra endomorphism of `Lambda L`
sending the formal power sum `p_k` to the axis generator `U_k` for every `k ≥ 1`.

It is the substitution whose bijectivity says that the axis generators are a system of free
generators of `Lambda L`, and its inverse is what turns a commuting family of slope operators
into a slope homomorphism. -/
@[hjo "def_axis_sub"]
noncomputable def axisSub (v : L) : Lambda L →ₐ[L] Lambda L :=
  MvPolynomial.aeval fun i => axisGen v (i + 1)

/-- The axis substitution on the generator `i` of `Lambda L`, which stands for `p_{i+1}`. -/
@[simp]
theorem axisSub_X (v : L) (i : ℕ) : axisSub v (MvPolynomial.X i) = axisGen v (i + 1) := by
  simp [axisSub]

/-- **The defining property of the axis substitution**: it sends `p_k` to `U_k` for every
`k ≥ 1`. -/
@[hjo "def_axis_sub"]
theorem axisSub_powerSum (v : L) {k : ℕ} (hk : 0 < k) :
    axisSub v (powerSum L k) = axisGen v k := by
  rw [powerSum, axisSub_X, Nat.sub_add_cancel hk]

end HJO.Sym
