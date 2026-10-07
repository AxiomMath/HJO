/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Defs
public import HJO.Evaluation.CollinearNarrowed
public import HJO.Shuffle.Grading
public meta import HJO.Attr

/-! # The compositional rational shuffle input, with the homogeneity removed

`HJO.External.Shuffle` is a conjunction of two clauses: the shuffle element
`(-1)^{N(b+1)} Θ(C_α 1) 1` is weighted homogeneous of degree `bN`, and in any realisation it
expands over the below-diagonal parking functions of return composition `α.reverse`. Only the
second clause is quoted from the literature -- Bergeron--Garsia--Leven--Xin (3.7) as proved by
Mellit, Section 6. The first is proved outright by tracking degrees through the three
constructions the element is built from, which is `HJO.Sym.shuffle_mem_lambdaComp`.

This file states the expansion clause on its own and proves that the two-clause assumption follows
from it, so that the redundancy of the homogeneity clause is a compiled fact rather than a claim. It
is additive: `HJO.External.Shuffle` is left as it is, and a statement that still takes it as a
hypothesis can be supplied from the narrowed form by `shuffle_of_narrowed`.

The narrowed clause is written with the sign outside the realisation;
`HJO.External.Shuffle` has it inside. The two are the same statement
because a realisation is an `L`-algebra homomorphism, hence `L`-linear, and `shuffle_of_narrowed`
crosses between them by `map_smul`.

The two genericity facts the homogeneity clause needs -- that `v = q u` is nonzero and not a root
of unity, which is what makes the axis generators free and so pins `Θ` off the axis generators --
come from the algebraic independence the quoted statement is already stated at, by
`HJO.CollinearNarrowed.mul_ne_zero_of_algebraicIndependent` and
`HJO.CollinearNarrowed.pow_succ_ne_one_of_algebraicIndependent`.
-/

@[expose] public section

open Finset

namespace HJO

open ParkingFunctions Paths

/-! ### The narrowed input -/

/-- **Bergeron--Garsia--Leven--Xin, equation (3.7)**, conjectured there and proved by **Mellit,
`Toric braids and (m,n)-parking functions`, Section 6**: in any realisation the shuffle element
`(-1)^{N(b+1)} Θ(C_α 1) 1` expands over the below-diagonal parking functions of return composition
`α.reverse` as `∑ q ^ dinv(π) u ^ area(P_π) F_{bN, ides(π)}`. This is the whole of what the cited
result supplies, and it is `HJO.External.Shuffle` without its first conjunct: the genericity
hypothesis is kept because that result works at generic parameters, but the homogeneity of the
shuffle element is no longer asked for. The sign sits outside the realisation, unlike in
`HJO.External.Shuffle`. -/
def ShuffleNarrowed (L : Type*) [Field L] [Algebra ℚ L] : Prop :=
  ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b →
    ∀ q u : L, AlgebraicIndependent ℤ ![q, u] →
      ∀ (ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L), Sym.IsRealisation ι →
        ∀ Θ : Sym.Lambda L →ₐ[L] Module.End L (Sym.Lambda L), Sym.IsSlopeHom a b q u Θ →
          ∀ N : ℕ, 0 < N → ∀ α : List ℕ, (∀ x ∈ α, 0 < x) → α.sum = N →
            (-1 : L) ^ (N * (b + 1)) • ι (Θ (Sym.CopComp q α 1) 1) =
              ∑ π ∈ withReturns α.reverse a b N, (q ^ dinv π * u ^ area (path π)) •
                gessel L (b * N) (ides π)

/-- **The homogeneity clause of the shuffle input is redundant.** The two-clause assumption
`HJO.External.Shuffle` follows from the expansion clause alone: the homogeneity it also asks for is
`HJO.Sym.shuffle_mem_lambdaComp`, whose two genericity hypotheses are supplied by the algebraic
independence the clause is already stated at and whose characteristic-zero hypothesis by the
rational algebra structure. The sign is moved inside the realisation by its `L`-linearity. -/
theorem shuffle_of_narrowed {L : Type*} [Field L] [Algebra ℚ L] (h : ShuffleNarrowed L) :
    HJO.External.Shuffle L := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  intro a b hab ha hb q u hqu ι hι Θ hΘ N hN α hαpos hαN
  refine ⟨?_, ?_⟩
  · exact Sym.mem_lambdaComp.1 (Sym.shuffle_mem_lambdaComp (by omega)
      (CollinearNarrowed.mul_ne_zero_of_algebraicIndependent hqu)
      (CollinearNarrowed.pow_succ_ne_one_of_algebraicIndependent hqu) hΘ hαN)
  · rw [map_smul]
    exact h a b hab ha hb q u hqu ι hι Θ hΘ N hN α hαpos hαN

end HJO
