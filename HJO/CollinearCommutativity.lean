/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.ShiftPair
public import HJO.Macdonald.Vocabulary
public meta import HJO.Attr

/-! # The displacement coefficients the collinear commutation is computed with

The bookkeeping the collinear commutation identity runs on: the passage between the one-variable
displacements `f[X + M/z]` and `f[X - M̃/z]`, the two-variable displacement
`f[X + M/z₁ - M̃/z₂]`, and their coefficients.

Four things are recorded. First, the one-variable displacement is recovered from its own
coefficients `f_{[s]}` over an explicit finite range: there is one bound `N`, depending on `f`
alone, beyond which every coefficient vanishes. Second, the two-variable displacement may be
computed in either order, so reading off one variable at a time gives a one-variable displacement of
a coefficient — `(f*_{[r]})[X + M/z₁]` along `z₂^{-r}` and `(f_{[s]})[X - M̃/z₂]` along `z₁^{-s}` —
and hence `f_{[s,r]}` is the iterated coefficient `(f*_{[r]})_{[s]}` and `(f_{[s]})*_{[r]}` alike.
Along either axis one of the two displacements is invisible, `f_{[s]} = f_{[s,0]}` and
`f*_{[r]} = f_{[0,r]}`, because a displacement fixes the coefficient of `z⁰`. Third, on the diagonal
`z₁ = q u z`, `z₂ = z` the two displacements cancel, so the two-variable displacement of `f`
specialises to `f` itself; this is the source of the alternating relations among the `f_{[s,r]}`.
Fourth, the displacement of `e₁`, which is `p₁` and therefore picks up exactly `M z^{-1}`.

## Main results

* `HJO.Sym.exists_bound_plethShift`.
* `HJO.Sym.plethShift_elemSymm_one`, the displacement of `e₁`, is not restated here: it is proved
  in `HJO/Collinear/Commutation.lean`.
* `HJO.Sym.plethShift_shiftStarCoeff`.
* `HJO.Sym.plethShiftStar_shiftCoeff`.
* `HJO.Sym.shiftCoeff_shiftStarCoeff`.
* `HJO.Sym.shiftStarCoeff_shiftCoeff`.
* `HJO.Sym.shiftCoeff_eq_shiftPairCoeff`.
* `HJO.Sym.shiftStarCoeff_eq_shiftPairCoeff`.
* `HJO.Sym.diagSpec_comp_plethShiftPair`.

## Implementation notes

**Both displacements are written in `w = z⁻¹`.** Each sends `p_k` to `p_k` plus a scalar multiple of
`z^{-k}`, so `HJO.Sym.plethShift` and `HJO.Sym.plethShiftStar` land in the polynomial ring `Λ[w]`
rather than in a ring of Laurent polynomials. Confinement to the nonpositive powers of `z` is
therefore carried by the target and is not a theorem; what `HJO.Sym.exists_bound_plethShift` asserts
here is the other half of it, the uniform bound and the reconstruction over `0 ≤ s < N` that it
supplies. The nonpositive subalgebra of a Laurent ring the proof passes through is available
separately (`HJO.Laurent.nonpositive`) and is not needed on this route.

**The two variables of the two-variable displacement are nested, not symmetric.**
`HJO.Sym.plethShiftPair` lands in `Λ[w₁][w₂]` with `w₂ = z₂⁻¹` outermost, so reading off the
coefficient of `z₂^{-r}` is a single `Polynomial.coeff` while reading off the coefficient of
`z₁^{-s}` is one after exchanging the two variables, the exchange being the ring isomorphism
`HJO.Sym.polySwap`. That asymmetry of *form*, and nothing mathematical, is the whole difference
between `HJO.Sym.plethShift_shiftStarCoeff` and `HJO.Sym.plethShiftStar_shiftCoeff` below.

**The vanishing along an axis is the constant coefficient of a displacement.** The usual proof shows
`f_{[s]} = f_{[s,0]}` by exhibiting the homomorphism `π` that reads off the coefficient of `z₂⁰` and
identifying `π ∘ δ₂` with `δ` on the generators `p_j`. Here that identification is the statement
that the starred displacement fixes the coefficient of `z⁰`, `HJO.Sym.shiftStarCoeff_zero`, whose
proof is the same computation on the generators; the two-variable coefficient at `r = 0` is then the
one-variable one. Symmetrically for `f*_{[r]} = f_{[0,r]}`.

**The diagonal specialisation, and why `q ≠ 0` and `u ≠ 0` are carried.** The specialisation
`ρ(z₁) = q u z`, `ρ(z₂) = z` is read in the inverse variables as `w₂ ↦ w`, `w₁ ↦ (q u)⁻¹ w`, which
is `HJO.Sym.diagSpec`. The lemma is stated as an equality of two ring homomorphisms out of `Λ`, the
specialised displacement against the inclusion `Λ → Λ[w]`, which is the form its proof takes: both
are algebra homomorphisms, so they agree as soon as they agree on the `p_j`. There the two displaced
terms are `(1-q^j)(1-u^j)(qu)^{-j}` and `(1-q^{-j})(1-u^{-j})`, equal exactly because `q` and `u`
are nonzero (`HJO.Sym.one_sub_inv_pow_mul`); at `q = 0` the first vanishes under Lean's `0⁻¹ = 0`
and the second does not, so the hypotheses are not removable. At the standing instance `𝕜 = ℚ(q, u)`
both are automatic.

## References

This file concerns the lemmas `HJO.Sym.exists_bound_plethShift`, `HJO.Sym.plethShift_elemSymm_one`,
`HJO.Sym.plethShift_shiftStarCoeff`, `HJO.Sym.plethShiftStar_shiftCoeff`,
`HJO.Sym.shiftCoeff_shiftStarCoeff`, `HJO.Sym.shiftStarCoeff_shiftCoeff`,
`HJO.Sym.shiftCoeff_eq_shiftPairCoeff`, `HJO.Sym.shiftStarCoeff_eq_shiftPairCoeff` and
`HJO.Sym.diagSpec_comp_plethShiftPair`, on the definitions `HJO.Sym.Lambda`, `HJO.Sym.elemSymm`,
`HJO.Sym.paramProduct`, `HJO.Sym.plethShift`, `HJO.Sym.plethShiftStar`, `HJO.Sym.plethShiftPair`,
`HJO.Sym.shiftCoeff`, `HJO.Sym.shiftStarCoeff` and `HJO.Sym.shiftPairCoeff`.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### The displacement is a finite sum of its coefficients -/

section Expansion

variable {L : Type*} [Field L]

/-- **The displacement is a finite sum of its coefficients.** For every
`f ∈ Λ` there is an `N ≥ 0` with `f_{[s]} = 0` for every `s ≥ N` and
`f[X + M/z] = ∑_{s=0}^{N-1} f_{[s]} z^{-s}`.

Read in `w = z⁻¹`, in which `HJO.Sym.plethShift` is written, the displacement is a polynomial over
`Λ`, so `N = deg + 1` serves: a polynomial has no coefficient above its degree and is the sum of its
monomials up to it. -/
@[hjo "lem_shift_expansion"]
theorem exists_bound_plethShift (q u : L) (f : Lambda L) :
    ∃ N : ℕ, (∀ s : ℕ, N ≤ s → shiftCoeff q u f s = 0) ∧
      plethShift q u f = ∑ s ∈ range N, Polynomial.monomial s (shiftCoeff q u f s) := by
  refine ⟨(plethShift q u f).natDegree + 1, fun s hs => ?_, ?_⟩
  · rw [shiftCoeff]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  · exact Polynomial.as_sum_range' _ _ (Nat.lt_succ_self _)

end Expansion

/-! ### The displacement of the first elementary function -/

section Elementary

variable {L : Type*} [Field L] [Algebra ℚ L]

end Elementary

/-! ### One variable at a time -/

section Pair

variable {L : Type*} [Field L]

/-- **The starred displacement first.** The element
`(f*_{[r]})[X + M/z₁]` is the coefficient of `z₂^{-r}` in `f[X + M/z₁ - M̃/z₂]`.

`HJO.Sym.plethShiftPair` is built as the starred displacement followed by the unstarred one applied
to each coefficient, so this is `Polynomial.coeff_map`, recorded pointwise as
`HJO.Sym.coeff_plethShiftPair`. -/
@[hjo "lem_shift_pair_star_first"]
theorem plethShift_shiftStarCoeff (q u : L) (f : Lambda L) (r : ℕ) :
    plethShift q u (shiftStarCoeff q u f r) = (plethShiftPair q u f).coeff r :=
  (coeff_plethShiftPair q u f r).symm

/-- **The unstarred displacement first.** The element
`(f_{[s]})[X - M̃/z₂]` is the coefficient of `z₁^{-s}` in `f[X + M/z₁ - M̃/z₂]`, the inner variable
being read as the outer one through the exchange `HJO.Sym.polySwap`.

Both sides are polynomials in `z₂^{-1}` over `Λ`, and their coefficients at `z₂^{-r}` agree: the
left-hand one is `(f_{[s]})*_{[r]}` and the right-hand one is the coefficient of `z₁^{-s}z₂^{-r}`,
which is `f_{[s,r]}`. -/
@[hjo "lem_shift_pair_shift_first"]
theorem plethShiftStar_shiftCoeff (q u : L) (f : Lambda L) (s : ℕ) :
    plethShiftStar q u (shiftCoeff q u f s)
      = (polySwap (Lambda L) (plethShiftPair q u f)).coeff s := by
  refine Polynomial.ext fun r => ?_
  rw [coeff_coeff_polySwap]
  exact (shiftPairCoeff_eq_shiftStarCoeff q u f s r).symm

/-- **Iterating the starred coefficient first.**
`(f*_{[r]})_{[s]} = f_{[s,r]}`.

Taking the coefficient of `z₁^{-s}` on both sides of `HJO.Sym.plethShift_shiftStarCoeff`; this is
how `HJO.Sym.plethShiftPair` is built, and the identity is recorded in the opposite orientation as
`HJO.Sym.shiftPairCoeff_eq_shiftCoeff`. -/
@[hjo "lem_shift_pair_iterate_star"]
theorem shiftCoeff_shiftStarCoeff (q u : L) (f : Lambda L) (s r : ℕ) :
    shiftCoeff q u (shiftStarCoeff q u f r) s = shiftPairCoeff q u f s r :=
  (shiftPairCoeff_eq_shiftCoeff q u f s r).symm

/-- **Iterating the unstarred coefficient first.**
`(f_{[s]})*_{[r]} = f_{[s,r]}`.

Taking the coefficient of `z₂^{-r}` on both sides of `HJO.Sym.plethShiftStar_shiftCoeff`; the
identity is recorded in the opposite orientation as `HJO.Sym.shiftPairCoeff_eq_shiftStarCoeff`, and
it is not formal, the two nestings of the two variables being exchanged by `HJO.Sym.polySwap`. -/
@[hjo "lem_shift_pair_iterate_plain"]
theorem shiftStarCoeff_shiftCoeff (q u : L) (f : Lambda L) (s r : ℕ) :
    shiftStarCoeff q u (shiftCoeff q u f s) r = shiftPairCoeff q u f s r :=
  (shiftPairCoeff_eq_shiftStarCoeff q u f s r).symm

/-- **The unstarred coefficient is a two-variable coefficient.**
`f_{[s]} = f_{[s,0]}`.

The two-variable coefficient at `r = 0` is the starred displacement's constant coefficient of
`f_{[s]}`, and a displacement fixes the coefficient of `z⁰`. -/
@[hjo "lem_shift_coeff_as_pair"]
theorem shiftCoeff_eq_shiftPairCoeff (q u : L) (f : Lambda L) (s : ℕ) :
    shiftCoeff q u f s = shiftPairCoeff q u f s 0 := by
  rw [shiftPairCoeff_eq_shiftStarCoeff, shiftStarCoeff_zero]

/-- **The starred coefficient is a two-variable coefficient.**
`f*_{[r]} = f_{[0,r]}`.

The same argument with the two variables exchanged: the two-variable coefficient at `s = 0` is the
unstarred displacement's constant coefficient of `f*_{[r]}`, which is `f*_{[r]}`. -/
@[hjo "lem_shift_star_coeff_as_pair"]
theorem shiftStarCoeff_eq_shiftPairCoeff (q u : L) (f : Lambda L) (r : ℕ) :
    shiftStarCoeff q u f r = shiftPairCoeff q u f 0 r := by
  rw [shiftPairCoeff_eq_shiftCoeff, shiftCoeff_zero]

end Pair

/-! ### The two displacements cancel on the diagonal -/

section Diagonal

variable {L : Type*} [Field L]

/-- **The two displacements cancel on the diagonal.** Suppose `q ≠ 0` and
`u ≠ 0` and let `ρ` be the `Λ`-algebra homomorphism with `ρ(z₁) = q u z` and `ρ(z₂) = z`. Then
`ρ(f[X + M/z₁ - M̃/z₂]) = f` for every `f ∈ Λ`, that is, `ρ` composed with the two-variable
displacement is the inclusion of `Λ`.

In the inverse variables `ρ` is `HJO.Sym.diagSpec`, and the assertion is that two ring
homomorphisms out of `Λ` agree; the pointwise form is `HJO.Sym.diagSpec_plethShiftPair`, proved by
comparing the two on the generators `p_j`, where the two displaced terms cancel because `q` and `u`
are nonzero. -/
@[hjo "lem_shift_pair_diagonal"]
theorem diagSpec_comp_plethShiftPair (q u : L) (hq : q ≠ 0) (hu : u ≠ 0) :
    (diagSpec q u).comp (plethShiftPair q u : Lambda L →+* Polynomial (Polynomial (Lambda L)))
      = (Polynomial.C : Lambda L →+* Polynomial (Lambda L)) :=
  RingHom.ext fun f => diagSpec_plethShiftPair q u hq hu f

end Diagonal

end HJO.Sym
