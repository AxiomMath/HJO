/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.PDeltaGraded
public meta import HJO.Attr

/-! # The swapping operator in the free variables

The piece of vocabulary of the graded ring that the lowering step needs and the rest of the
development does not state: the operator whose existence is the content of
`HJO.Sym.existsUnique_mem_pGraded_xdeltaNum_eq`. For `r ≥ 0` and `G` in the graded part `P^gr_{k,d}`
of `P°_k`, `Δ_{x_r,x_{r+1}}(G)` is the unique `H ∈ P^gr_{k,d}` with

`(x_{r+1} - x_r)H = (q-1)x_{r+1}G + (x_{r+1} - qx_r)ŝ_{x_r,x_{r+1}}(G)`,

where `ŝ_{x_r,x_{r+1}}` interchanges the two free variables. Unlike the operator `Δ_i` in the
*auxiliary* variables, this one is not obtained by performing the division: `x_{r+1} - x_r` has no
constant term, hence is not invertible in `P°_k`, and the quotient exists because the right-hand
side vanishes on identifying the two variables. So the defining property, and not a formula, is how
the operator is to be used, and this file states it.

## Main results

* `HJO.Sym.X_sub_X_mul_xdelta`: the displayed equation, holding for every series.
* `HJO.Sym.eq_xdelta_of_X_sub_X_mul_eq`: the equation has at most one solution in `P°_k`.
* `HJO.Sym.eq_xdelta_iff`: `Δ_{x_r,x_{r+1}}(G)` is *the* element of `P^gr_{k,d}` solving the
  equation — the definition in the form in which it is stated.

## Implementation notes

*The operator is `HJO.Sym.xdelta`*, the quotient that
`HJO.Sym.existsUnique_mem_pGraded_xdeltaNum_eq` produces. The equations here replace its
construction: a reader needs the displayed identity and the uniqueness that pins the solution down,
never the coefficient formula for the quotient.

*Uniqueness needs neither the grading nor the graded part.* One usually asks for the unique
solution in `P^gr_{k,d}`, but a solution is unique in all of `P°_k`: the divisor `x_{r+1} - x_r` is
a nonzero element of a domain, so it cancels. Symmetrically, the equation is solvable for every
`G ∈ P°_k`, since the numerator vanishes on the diagonal whatever `G` is; what the grading buys is
that the solution then lies in `P^gr_{k,d}` again, which is `HJO.Sym.xdelta_mem_pGraded`. The
grading hypothesis therefore appears only in `HJO.Sym.eq_xdelta_iff`, where the statement quantifies
over solutions *in the graded part*.

*The free variables are indexed from `0`*, so the `x_r`, `x_{r+1}` for `r ≥ 0` are
`MvPowerSeries.X r` and `MvPowerSeries.X (r + 1)` for every `r : ℕ`, and the level `k` is
unconstrained: nothing here reads it, where the auxiliary operator needs `k ≥ 2` for a variable
`y_{i+1}` to exist.

*The parameter `q` enters through `HJO.Sym.scalarFrac`*, its image in the coefficient field
`𝕂(y_1, …, y_k)`, and the numerator is written with `C q - 1` rather than `C (q - 1)`, as in
`HJO.Sym.xdeltaNum`.

## References

E. Carlsson and
A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697,
Section 4, where the operator is written as a fraction and the division is not justified.
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K] {k d : ℕ}

/-- **The defining equation of the swapping operator in the free variables**:

`(x_{r+1} - x_r)Δ_{x_r,x_{r+1}}(G) = (q-1)x_{r+1}G + (x_{r+1} - qx_r)ŝ_{x_r,x_{r+1}}(G)`.

No hypothesis is needed: the numerator vanishes on identifying `x_r` with `x_{r+1}` for every
series, so the quotient solves the equation whether or not `G` is graded. -/
@[hjo "def_cm_xdelta"]
theorem X_sub_X_mul_xdelta (q : K) (r : ℕ) (G : AuxAlphabetSeriesFrac K k) :
    (MvPowerSeries.X (r + 1) - MvPowerSeries.X r) * xdelta q r G =
      (MvPowerSeries.C (scalarFrac K q) - 1) * MvPowerSeries.X (r + 1) * G
        + (MvPowerSeries.X (r + 1) - MvPowerSeries.C (scalarFrac K q) * MvPowerSeries.X r)
          * xswap K k r (r + 1) G :=
  ((xdeltaNum_apply q r G).symm.trans (xdeltaNum_eq_X_sub_X_mul_xdelta q r G)).symm

/-- **The defining equation has at most one solution**, and it is `Δ_{x_r,x_{r+1}}(G)`: the divisor
`x_{r+1} - x_r` is a nonzero element of the domain `P°_k`, so it cancels. The
requirement that the solution lie in `P^gr_{k,d}` is not needed for this, nor is any hypothesis
on `G`. -/
theorem eq_xdelta_of_X_sub_X_mul_eq [IsDomain K] {q : K} {r : ℕ}
    {G H : AuxAlphabetSeriesFrac K k}
    (h : (MvPowerSeries.X (r + 1) - MvPowerSeries.X r) * H =
      (MvPowerSeries.C (scalarFrac K q) - 1) * MvPowerSeries.X (r + 1) * G
        + (MvPowerSeries.X (r + 1) - MvPowerSeries.C (scalarFrac K q) * MvPowerSeries.X r)
          * xswap K k r (r + 1) G) :
    H = xdelta q r G :=
  mul_left_cancel₀ (X_sub_X_ne_zero (Nat.ne_of_lt (Nat.lt_succ_self r)))
    (h.trans (X_sub_X_mul_xdelta q r G).symm)

/-- **The swapping operator in the free variables**: for `G ∈ P^gr_{k,d}`, the element
`Δ_{x_r,x_{r+1}}(G)` is the unique `H ∈ P^gr_{k,d}` with

`(x_{r+1} - x_r)H = (q-1)x_{r+1}G + (x_{r+1} - qx_r)ŝ_{x_r,x_{r+1}}(G)`.

Read left to right this is uniqueness, read right to left it is existence together with the
statement that the value again has free-variable degree `d`. -/
@[hjo "def_cm_xdelta"]
theorem eq_xdelta_iff [IsDomain K] (q : K) (r : ℕ) {G H : AuxAlphabetSeriesFrac K k}
    (hG : G ∈ pGraded K k d) :
    H = xdelta q r G ↔ H ∈ pGraded K k d ∧
      (MvPowerSeries.X (r + 1) - MvPowerSeries.X r) * H =
        (MvPowerSeries.C (scalarFrac K q) - 1) * MvPowerSeries.X (r + 1) * G
          + (MvPowerSeries.X (r + 1) - MvPowerSeries.C (scalarFrac K q) * MvPowerSeries.X r)
            * xswap K k r (r + 1) G := by
  refine ⟨fun h => ?_, fun h => eq_xdelta_of_X_sub_X_mul_eq h.2⟩
  subst h
  exact ⟨xdelta_mem_pGraded q r hG, X_sub_X_mul_xdelta q r G⟩

end HJO.Sym
