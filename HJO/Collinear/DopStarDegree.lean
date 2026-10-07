/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.DopStarPair
public import HJO.Collinear.ShiftStarGraded
public meta import HJO.Attr

/-! # The starred displacement as a finite sum, and the degree of a starred operator

Three lemmas about `D*_k` and the starred displacement: that `f[X - M̃/z]` is recovered
from its own coefficients over an explicit finite range, that `D*_k` is `𝕜`-linear, and that `D*_b`
raises the homogeneous degree by exactly `b`.

## Main results

* `HJO.Sym.exists_bound_plethShiftStar`.
* `HJO.Sym.isLinearMap_dopStar`.
* `HJO.Sym.dopStar_mem_lambdaComp`.

## Implementation notes

**What `HJO.Sym.exists_bound_plethShiftStar` asserts here.** The statement drops the clause "the
displacement involves no positive power of `z`" as discharged by the encoding --
`HJO.Sym.plethShiftStar` lands in `Λ[w]` for `w = z⁻¹` by construction -- and keeps two things: the
*uniform* bound `N`, depending on `f` alone, beyond which every coefficient vanishes, and the
reconstruction of the displacement as a sum over the explicit range `0 ≤ r < N`. Both are in the
statement below, in the shape `HJO.Sym.exists_bound_plethShiftPair` already uses for the
two-variable displacement: one `∃ N` carrying a vanishing clause and an equation.

**`HJO.Sym.isLinearMap_dopStar` is discharged by the encoding, and is stated anyway.**
`HJO.Sym.DopStar q u k` is a `Module.End L (Lambda L)`, so its linearity is not a theorem but the
type it inhabits; the proof, which runs through the expansion in displacement
coefficients, is proving something the definition already gives. It is stated as an
`IsLinearMap` so that a consumer has the statement to quote.

**No side condition anywhere in this file.** The starred displacement's scalars are
`1 - (q ^ j)⁻¹`, which are defined at every `q` including `0` (Lean's `0⁻¹ = 0`), and nothing here
divides. In particular `HJO.Sym.dopStar_mem_lambdaComp` holds at every `q` and `u`.

## References

This file proves `HJO.Sym.exists_bound_plethShiftStar`, `HJO.Sym.isLinearMap_dopStar` and
`HJO.Sym.dopStar_mem_lambdaComp`, about the definitions `HJO.Sym.plethShiftStar`,
`HJO.Sym.shiftStarCoeff`, `HJO.Sym.DopStar`, `HJO.Sym.LambdaComp`.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### The starred displacement is a finite sum of its coefficients -/

section Expansion

variable {L : Type*} [Field L]

/-- **The starred displacement is a finite sum of its coefficients.**
For every `f ∈ Λ` there is an `N ≥ 0` with `f*_{[r]} = 0` for every `r ≥ N` and
`f[X - M̃/z] = ∑_{r=0}^{N-1} f*_{[r]} z^{-r}`.

Read in `w = z⁻¹`, in which `HJO.Sym.plethShiftStar` is written, the displacement is a polynomial
over `Λ`, so `N = deg + 1` serves: a polynomial has no coefficient above its degree and is the sum
of its monomials up to it. -/
@[hjo "lem_shift_star_expansion"]
theorem exists_bound_plethShiftStar (q u : L) (f : Lambda L) :
    ∃ N : ℕ, (∀ r : ℕ, N ≤ r → shiftStarCoeff q u f r = 0) ∧
      plethShiftStar q u f
        = ∑ r ∈ range N, Polynomial.monomial r (shiftStarCoeff q u f r) := by
  refine ⟨(plethShiftStar q u f).natDegree + 1, fun r hr => ?_, ?_⟩
  · rw [shiftStarCoeff]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  · exact Polynomial.as_sum_range' _ _ (Nat.lt_succ_self _)

/-- The coefficients of the starred displacement vanish above its degree, which is the vanishing
half of `HJO.Sym.exists_bound_plethShiftStar` at the explicit bound the proof above takes. -/
theorem shiftStarCoeff_eq_zero_of_natDegree_lt (q u : L) (f : Lambda L) {r : ℕ}
    (hr : (plethShiftStar q u f).natDegree < r) : shiftStarCoeff q u f r = 0 := by
  rw [shiftStarCoeff]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt hr

end Expansion

/-! ### The starred operators are linear -/

section Linear

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The starred operators are linear.** For every `k ≥ 0` the map `D*_k` is
`𝕜`-linear from `Λ` to `Λ`.

`HJO.Sym.DopStar q u k` is by construction the composite of the `𝕜`-algebra homomorphism
`HJO.Sym.plethShiftStar` with the `𝕜`-linear pairing `HJO.Sym.coeffPairing`, so it inhabits
`Module.End L (Lambda L)` and the linearity is discharged by the encoding; the statement is
recorded so that it can be quoted. -/
@[hjo "lem_dopstar_linear"]
theorem isLinearMap_dopStar (q u : L) (k : ℕ) : IsLinearMap L (DopStar q u k) :=
  ⟨fun f g => (DopStar q u k).map_add f g, fun c f => (DopStar q u k).map_smul c f⟩

end Linear

/-! ### The starred operators raise the degree by the index -/

section Degree

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The starred operators raise the degree by the index.** For
`f ∈ Λ_d` and `b ≥ 0`, `D*_b f ∈ Λ_{d+b}`.

`D*_b f = ∑_{r ≥ 0} f*_{[r]} h_{r+b}`, a sum that stops at `r = d` because the coefficients of the
starred displacement of a degree-`d` element do (`HJO.Sym.shiftStarCoeff_eq_zero_of_lt`). In the
surviving terms `f*_{[r]} ∈ Λ_{d-r}` and `h_{r+b} ∈ Λ_{r+b}`, and `(d-r) + (r+b) = d+b` since
`r ≤ d`. -/
@[hjo "lem_ght_dopstar_component"]
theorem dopStar_mem_lambdaComp (q u : L) (b : ℕ) {d : ℕ} {f : Lambda L}
    (hf : f ∈ LambdaComp L d) : DopStar q u b f ∈ LambdaComp L (d + b) := by
  rw [dopStar_eq_sum_range q u b f (N := d + 1)
    fun r hr => shiftStarCoeff_eq_zero_of_lt q u hf (by omega)]
  refine Submodule.sum_mem _ fun r hr => ?_
  have hrd : r ≤ d := by
    have := Finset.mem_range.1 hr
    omega
  have hmem := mul_mem_lambdaComp (shiftStarCoeff_mem_lambdaComp q u hf hrd)
    (completeHomog_mem_lambdaComp L (r + b))
  rwa [show d - r + (r + b) = d + b from by omega] at hmem

end Degree

end HJO.Sym
