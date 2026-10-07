/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.PieriDischarge
public import HJO.Macdonald.PieriSupport
public meta import HJO.Attr

/-! # The collinear input costs `HasPfunPieriSupport`, and nothing else

`HJO/Collinear/PieriDischarge.lean` reduced the collinear input to one `Prop` at one field,
`HJO.Sym.HasPieriEigenfamily (paramQ K) (paramU K)`. This file takes the reduction one step further
and off that predicate entirely: the collinear input costs
`HJO.Sym.HasPfunPieriSupport` -- `HJO.Standing.hasPfunPieriSupport_param` -- and nothing else.

## Why the step is free

`HJO.Standing.hasPieriEigenfamily_macHtilde_param` already derives `HasPieriEigenfamily` from
exactly two hypotheses, `hdop` and `hP`. The first of them, Garsia--Haiman--Tesler's Theorem 1.2
equation (1.11)a, is not a hypothesis: it is `HJO.Standing.dop_zero_smul_macHtilde_param`, proved
outright, whose own last input is GHT (4.24), that is `HJO.Sym.isEopEigenJfun`. So supplying it
leaves `hP`.

That the step is free is worth recording rather than leaving implicit, because the two hypotheses
look symmetric and are not: `hdop` is a theorem, so only `hP` carries content.

## What `HasPfunPieriSupport` is, and what remains below it

It is the statement that `e_1 P_ν` lies in the span of the `P_λ` with `λ` covering `ν` -- Pieri
support for Macdonald's `P`, as opposed to for the modified family `H̃`. The route to it is the
Macdonald duality block, and that block is unavoidable, as a counterexample shows: at
`ν = (3,2,2,1)` the partition `λ = (3,3,1,1,1)` survives dominance triangularity, the
lex leading exponent, `λ₁ ≤ ν₁` and the column-removal induction all at once, while the conjugate
partitions exclude it immediately.

## The chain, end to end

With this file the collinear side of the library reads, from the top:

* `HJO.External.CollinearCommutation L`, at every coefficient field, from
* `HJO.CollinearNarrowed.collinearCommutation_of_pfunPieriSupport` below, from
* `HJO.Sym.HasPfunPieriSupport` at the standing field, and nothing else.

Everything between -- the Euclidean descent on the slope operators, the ascent from `𝕜` to the
model's coefficient field, the index shift, the unnormalised Macdonald eigenbasis, the modified
family, the `D_0` relation, and every parameter condition any of them needs -- is a theorem.
-/

@[expose] public section

namespace HJO.Standing

open HJO.Sym HJO.Ascent

variable (K : Type*) [Field K] [Algebra ℚ K] [Algebra ParamRing K] [IsFractionRing ParamRing K]

/-- **The Pieri eigenfamily at the standing field, from the `P`-side Pieri support alone.**

`HJO.Standing.hasPieriEigenfamily_macHtilde_param` with its `hdop` supplied by
`HJO.Standing.dop_zero_smul_macHtilde_param`, which is a theorem. -/
theorem hasPieriEigenfamily_param
    (hP : HasPfunPieriSupport (q := paramQUnit K) (u := paramU K)
      (algebraicIndependent_paramQUnit K)) :
    HasPieriEigenfamily (paramQ K) (paramU K) :=
  hasPieriEigenfamily_macHtilde_param K (dop_zero_smul_macHtilde_param K) hP

end HJO.Standing

namespace HJO.CollinearNarrowed

open HJO.Sym HJO.Ascent HJO.Standing

variable (K : Type*) [Field K] [Algebra ℚ K] [Algebra ParamRing K] [IsFractionRing ParamRing K]

/-- **The collinear input, from `HasPfunPieriSupport` at the standing field and nothing else.**

`HJO.External.CollinearCommutation L` for an arbitrary field `L` of characteristic zero, given only
`HJO.Standing.hasPfunPieriSupport_param` at `𝕜`.

This strengthens `HJO.CollinearNarrowed.collinearCommutation_of_pieri_param` as the statement of
what the collinear side costs, in the same way that theorem strengthens
`collinearCommutation_of_structures`. Each step removes a hypothesis of the previous statement that
is a theorem. -/
theorem collinearCommutation_of_pfunPieriSupport
    (hP : HasPfunPieriSupport (q := paramQUnit K) (u := paramU K)
      (algebraicIndependent_paramQUnit K))
    (L : Type*) [Field L] [Algebra ℚ L] : HJO.External.CollinearCommutation L :=
  collinearCommutation_of_pieri_param K (hasPieriEigenfamily_param K hP) L

end HJO.CollinearNarrowed
