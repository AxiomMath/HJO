/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepStandardisation
public meta import HJO.Attr

/-! # The rewriting of the right-hand side of the compositional rational shuffle identity

The right-hand side of the compositional rational shuffle identity is a sum over the above-diagonal
parking functions of return composition `α`,
`∑_{π̂ ∈ PF̂^α_{aN,bN}} q^{d̂inv(π̂)} u^{ârea(P̂_π̂)} F_{bN, îdes(π̂)^{∨bN}}`; what the sweep
process computes is a sum over *paths*,
`∑_{P̂} u^{ârea(P̂)} q^{ĥ(P̂) - max t̂dinv(P̂)} χ(P̂)` over the above-diagonal `(aN, bN)`-paths of
return composition `α`. This file records that a symmetric function `f` whose image under a
realisation is the first sum has that image equal to the second, which is the form the sweep
process meets.

The two sums are equal in `𝒫 = K⟦x₁, x₂, …⟧` outright. Grouping the parking functions by their
underlying path, the members of `PF̂^α_{aN,bN}` lying over `P̂` are all the labellings of `P̂` when
the return composition of `P̂` is `α` and none otherwise, while `ârea(P̂_π̂)` depends only on `P̂`;
writing `d̂inv(π̂) = ĥ(P̂) + t̂dinv(π̂) - max t̂dinv(P̂)`, the equality reduces to one identity per
path, `χ(P̂) = ∑_{π̂} q^{t̂dinv(π̂)} F_{bN, îdes(π̂)^{∨bN}}` over the labellings `π̂` of `P̂`,
and that identity is the standardisation bijection: a word on the north steps of `P̂` whose
letters strictly decrease along every marked pair determines, and is determined by its exponent
vector together with, the labelling that lists the north steps in decreasing order of letter with
ties broken by rank.

## Main results

* `HJO.Mellit.eq_sum_sweepChar_of_eq_sum_gessel`: the rewriting, `ι f` being carried from the
  parking-function sum to the path sum.

## Implementation notes

The mathematics is the equality of the two sums, `HJO.Mellit.sum_sweepChar_eq_sum_gessel`, whose
per-path input is `HJO.ParkingFunctions.sweepChar_eq_sum_gessel`; the realisation and `f` enter only
to name the left-hand side, and the rewriting is that equality read at `ι f`.

Three hypotheses of the statement as usually written are absent here. `ι` is not assumed to be a
realisation (`HJO.Sym.IsRealisation`): the two sums agree as elements of `𝒫`, so the rewriting holds
of the image of `f` under any algebra map, and the realisation axiom is never read. `N ≥ 1` and "`α`
is a composition of `N`" are likewise unnecessary, both index sets being cut out by
`HJO.Paths.HasAboveReturns`, which carries those conditions itself; when they fail the identity is
vacuous rather than false.

Two hypotheses are present that are usually left to standing conventions. `0 < a` is what
survives of the standing `1 < a < b`, and it is what makes the above-diagonal rank injective on the
north steps of a path, hence the reading order used by the standardisation a strict total order. And
`q ≠ 0` is needed to combine `q^{ĥ - max t̂dinv}` with `q^{t̂dinv}` into `q^{d̂inv}`: the exponent
`ĥ(P̂) - max t̂dinv(P̂)` is genuinely negative on most above-diagonal paths, so the two sides do
not agree at `q = 0`. The coefficient field `𝕜 = ℚ(q, u)`
supplies it, `q` being an indeterminate.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, arXiv:1604.07456, section
"The sweep process".
-/

@[expose] public section

namespace HJO.Mellit

open ParkingFunctions Paths

/-- **The rewriting of the right-hand side.** If the image of `f ∈ Λ` under
a realisation `ι` is the parking-function form of the right-hand side,
`ι(f) = ∑_{π̂ ∈ PF̂^α_{aN,bN}} q^{d̂inv(π̂)} u^{ârea(P̂_π̂)} F_{bN, îdes(π̂)^{∨bN}}`, then it is the
path form,
`ι(f) = ∑_{P̂} u^{ârea(P̂)} q^{ĥ(P̂) - max t̂dinv(P̂)} χ(P̂)`, the sum over the above-diagonal
`(aN, bN)`-paths of return composition `α`.

The two sums are equal in `𝒫` by `HJO.Mellit.sum_sweepChar_eq_sum_gessel`, which groups the parking
functions by their underlying path and appeals to the standardisation bijection on each; `ι` and `f`
name the left-hand side and nothing more, so no property of `ι` is read. The module docstring says
which hypotheses of the statement are dropped and where `0 < a` and `q ≠ 0` are
spent. -/
@[hjo "lem_sweep_rhs_rewrite"]
theorem eq_sum_sweepChar_of_eq_sum_gessel {L : Type*} [Field L] {a b : ℕ} {q u : L} (ha : 0 < a)
    (hq : q ≠ 0) (N : ℕ) (α : List ℕ) {ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L}
    {f : Sym.Lambda L}
    (hf : ι f = ∑ π ∈ aboveWithReturns α a b N,
      (q ^ aboveDinv π * u ^ Paths.aboveArea (abovePath π)) •
        gessel L (b * N) (descentReverse (b * N) (aboveIdes π))) :
    ι f = ∑ y ∈ aboveReturnPaths a b N α,
      (u ^ Paths.aboveArea y *
          q ^ ((Paths.aboveHookCount y : ℤ) - (aboveMaxTdinv y : ℤ))) • Paths.sweepChar q y :=
  hf.trans (sum_sweepChar_eq_sum_gessel ha hq N α).symm

end HJO.Mellit
