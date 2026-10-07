/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.CommutationTheorem
public import HJO.Shuffle.LhsAscent
public import HJO.Shuffle.MellitThm58Closed

/-! # Everything downstream of the compositional rational shuffle identity

The shuffle side of this library produces one `Prop`, `HJO.External.Shuffle L`: the
below-diagonal compositional rational shuffle identity of Bergeron–Garsia–Leven–Xin, proved by
Mellit, together with the homogeneity of the shuffle element. This file derives from it every
statement the library needs downstream of that identity, so that each is one application once
the identity itself is a theorem.

The first observation is that the passage `HJO.shuffle_of_shuffleAbove` from the above-diagonal
form `HJO.ShuffleAbove` is an equivalence. Its converse reindexes the above-diagonal sum along the
half turn of the rectangle (`HJO.sum_aboveWithReturns_eq`), which reverses the composition and
reflects every inverse descent set, and the reflection is absorbed by the Gessel reversal
`HJO.gessel_reverse_sum` applied to the below-diagonal expansion. Both steps are theorems, so the
two forms of the shuffle identity are interchangeable, at every field.

The remaining statements are the forms in which the identity is read: `HJO.shuffleAbove` (the
above-diagonal form), the expansion with the sign outside the realisation
(`HJO.Ascent.realisation_shuffle_eq_sum_of_shuffle`), `HJO.Sym.shuffle_mem_lambdaComp` (the first
clause, which needs nothing) and `HJO.Ascent.shuffle` (the identity itself at every field), and the
two objectives of the challenge file over the shuffle input alone.

## Main results

* `HJO.shuffleAbove_of_shuffle`, `HJO.shuffleAbove_iff_shuffle`: the above- and below-diagonal
  forms of the shuffle identity are equivalent.
* `HJO.shuffleNarrowed_of_shuffle`, `HJO.shuffleNarrowed_iff_shuffle`: the homogeneity clause of
  `HJO.External.Shuffle` is redundant, in both directions.
* `HJO.Ascent.realisation_shuffle_eq_sum_of_shuffle`: the expansion with the sign outside `ι`.
* `HJO.Ascent.shuffle_mem_lambdaComp_of_algebraicIndependent`: the homogeneity clause at
  algebraically independent parameters, unconditionally.
* `HJO.Ascent.shuffle_of_lhsWord_standing`: `HJO.External.Shuffle L` at every field `L` from the
  word form of Mellit's left-hand side at the standing field alone.
* `HJO.Ascent.conjecture_of_lhsWord_standing`, `HJO.Ascent.finiteSeries_eq_of_lhsWord_standing`:
  the two objectives from that one hypothesis.

## Implementation notes

The expansion with the sign outside the realisation is naturally stated at every coprime pair with
`a, b ≥ 1`, but its proof reads `HJO.External.Shuffle` at the standing instance, and
`HJO.External.Shuffle` lives under the standing convention `1 < a < b`. So the version proved here,
from `HJO.External.Shuffle`, carries `1 < a` and `a < b`;
the pairs with `a = 1` or `a > b` are not reached by the identity in the form proved here.

## References

This file concerns `HJO.shuffleAbove`, `HJO.External.Shuffle`, `HJO.Sym.shuffle_mem_lambdaComp`,
`HJO.Ascent.realisation_shuffle_eq_sum_of_shuffle` and `HJO.Ascent.shuffle`.
-/

@[expose] public section

open Finset

namespace HJO

open ParkingFunctions Paths

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The homogeneity clause can be dropped.** The expansion clause of `HJO.External.Shuffle`, with
the sign moved outside the realisation by its `L`-linearity, is `HJO.ShuffleNarrowed`. -/
theorem shuffleNarrowed_of_shuffle (h : External.Shuffle L) : ShuffleNarrowed L := by
  intro a b hab ha hb q u hqu ι hι Θ hΘ N hN α hαpos hαN
  have h2 := (h a b hab ha hb q u hqu ι hι Θ hΘ N hN α hαpos hαN).2
  rwa [map_smul] at h2

/-- **The shuffle input is its expansion clause**: the homogeneity clause is a theorem. -/
theorem shuffleNarrowed_iff_shuffle : ShuffleNarrowed L ↔ External.Shuffle L :=
  ⟨shuffle_of_narrowed, shuffleNarrowed_of_shuffle⟩

/-- **The above-diagonal shuffle identity from the below-diagonal one.** This is the
converse of `HJO.shuffle_of_shuffleAbove`. -/
theorem shuffleAbove_of_shuffle (h : External.Shuffle L) : ShuffleAbove L := by
  intro a b hab ha hb q u hqu ι hι Θ hΘ N hN α hαpos hαN
  rw [sum_aboveWithReturns_eq (by omega) hN q u α]
  have hres := gessel_reverse_sum ι hι (b * N) (ParkingFunction a b N)
    (withReturns α.reverse a b N) (fun π => q ^ dinv π * u ^ area (path π)) ides
    (fun π _ => ides_subset π) _ (h a b hab ha hb q u hqu ι hι Θ hΘ N hN α hαpos hαN).2
  rwa [map_smul] at hres

/-- **The two orientations of the shuffle identity are equivalent**, at every field. -/
theorem shuffleAbove_iff_shuffle : ShuffleAbove L ↔ External.Shuffle L :=
  ⟨shuffle_of_shuffleAbove, shuffleAbove_of_shuffle⟩

end HJO

namespace HJO.Ascent

open HJO.Sym HJO.ParkingFunctions HJO.Paths

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The shuffle element is homogeneous of degree `bN` at algebraically independent
parameters.** `HJO.Sym.shuffle_mem_lambdaComp`, whose two conditions on the parameters follow from
their algebraic independence. -/
theorem shuffle_mem_lambdaComp_of_algebraicIndependent {x y : L}
    (h : AlgebraicIndependent ℤ ![x, y]) {a b : ℕ} (hb : 0 < b)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom a b x y Θ) {α : List ℕ} {N : ℕ}
    (hα : α.sum = N) :
    (-1 : L) ^ (N * (b + 1)) • Θ (CopComp x α 1) 1 ∈ LambdaComp L (b * N) :=
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  shuffle_mem_lambdaComp hb (CollinearNarrowed.mul_ne_zero_of_algebraicIndependent h)
    (CollinearNarrowed.pow_succ_ne_one_of_algebraicIndependent h) hΘ hα

/-- **The compositional rational shuffle expansion at algebraically independent parameters**, with
the sign outside the realisation, from `HJO.External.Shuffle L`, at coprime `1 < a < b`. -/
theorem realisation_shuffle_eq_sum_of_shuffle (hS : External.Shuffle L) {x y : L}
    (h : AlgebraicIndependent ℤ ![x, y]) {a b : ℕ} (hab : Nat.Coprime a b) (ha : 1 < a)
    (hb : a < b) {ι : Lambda L →ₐ[L] AlphabetSeries L} (hι : IsRealisation ι)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom a b x y Θ) {N : ℕ} (hN : 0 < N)
    {α : List ℕ} (hαpos : ∀ r ∈ α, 0 < r) (hα : α.sum = N) :
    (-1 : L) ^ (N * (b + 1)) • ι (Θ (CopComp x α 1) 1) =
      ∑ π ∈ withReturns α.reverse a b N,
        (x ^ dinv π * y ^ area (path π)) • gessel L (b * N) (ides π) :=
  shuffleNarrowed_of_shuffle hS a b hab ha hb x y h ι hι Θ hΘ N hN α hαpos hα

/-- **The shuffle identity at every field, from Mellit's left-hand side at the standing field.**
The word form `HJO.Mellit.LhsWord` at the two indeterminates of `𝕜` ascends to every pair of
algebraically independent parameters (`HJO.Mellit.lhsComputes_of_lhsWord_standing`), and
`HJO.Mellit.shuffle_of_lhs` turns that into `HJO.External.Shuffle L`. -/
theorem shuffle_of_lhsWord_standing
    (hw : ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b →
      Mellit.LhsWord (paramQ Kk) (paramU Kk) a b)
    (L : Type*) [Field L] [Algebra ℚ L] : External.Shuffle L :=
  Mellit.shuffle_of_lhs (Mellit.lhsComputes_of_lhsWord_standing Kk hw)

/-- **The Huang–Jiang–Oblomkov conjecture from Mellit's left-hand side at the standing field.** -/
theorem conjecture_of_lhsWord_standing
    (hw : ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b →
      Mellit.LhsWord (paramQ Kk) (paramU Kk) a b)
    {a b : ℕ} (hab : Nat.Coprime a b) (ha : 1 < a) (hb : a < b) : HJO.Conjecture a b :=
  Debt.conjecture_of_shuffle (shuffle_of_lhsWord_standing hw _) hab ha hb

/-- **The finite identity from Mellit's left-hand side at the standing field.** -/
theorem finiteSeries_eq_of_lhsWord_standing
    (hw : ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b →
      Mellit.LhsWord (paramQ Kk) (paramU Kk) a b)
    {a b : ℕ} (hab : Nat.Coprime a b) (ha : 1 < a) (hb : a < b) (N : ℕ) :
    Gaps.finiteSeries a b N =
      qPochhammer PowerSeries.X PowerSeries.X N * HJO.Cylindric.boundedGF a b N :=
  Debt.finiteSeries_eq_of_shuffle (shuffle_of_lhsWord_standing hw _) hab ha hb N

end HJO.Ascent
