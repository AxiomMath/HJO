/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.PfunSupportDischarge
public import HJO.Main.Final
public import HJO.Macdonald.PieriSupportFull
public import HJO.Shuffle.GesselReversal
public meta import HJO.Attr

/-! # The collinear commutation input, unconditionally

The commutation of slope operators along a line through the origin,
`HJO.External.CollinearCommutation L`, holds at every field `L` of characteristic zero with no
hypothesis (`HJO.Debt.collinearCommutation_general`). The Macdonald-polynomial argument runs at
the standing coefficient field `𝕜 = ℚ(q, u)`, where the two parameters are indeterminates and
admit the inversions the argument needs, and `HJO.Ascent.commute_qop_ascend` carries the
commutation from there to any `L`.

The file then records the finite identity and the Huang--Jiang--Oblomkov conjecture over the
shuffle input `HJO.External.Shuffle Base` alone (`HJO.Debt.finiteSeries_eq_of_shuffle`,
`HJO.Debt.conjecture_of_shuffle`), and over `HJO.ShuffleAbove Base`, the raw above-diagonal
expansion of Mellit's Section 6 (`HJO.Debt.finiteSeries_eq_of_debt`,
`HJO.Debt.conjecture_of_debt`). The unconditional theorems are
`HJO.finiteSeries_eq_qPochhammer_mul_boundedGF` and `HJO.conjecture`.

## Main statements

* `HJO.Debt.collinearCommutation_general`: the collinear commutation input at every field of
  characteristic zero.
* `HJO.Debt.collinearCommutation`: the same at the standing instance `Base`.
* `HJO.Debt.finiteSeries_eq_of_shuffle`, `HJO.Debt.conjecture_of_shuffle`: the two main results
  over the shuffle input.
* `HJO.Debt.finiteSeries_eq_of_debt`, `HJO.Debt.conjecture_of_debt`: the same over
  `HJO.ShuffleAbove`.

## References

A. Mellit, *Toric braids and (m,n)-parking functions*, arXiv:1604.07456.
-/

/-! ## The collinear input
-/

@[expose] public section

namespace HJO.Debt

open Finset
open HJO.Sym HJO.ReesRegular HJO.PhiMul
open HJO.PhiMul.Witness (Base)

/-- **The collinear input, unconditionally**, at every field `L` of characteristic zero.

The proof needs one `Prop` at the standing coefficient field `𝕜 = ℚ(q, u)`,
`HJO.Standing.hasPfunPieriSupport_param`, and that `Prop` is a theorem, so this has no
hypothesis. The Macdonald argument runs at `𝕜` and only there: it goes through
`HJO.Sym.exists_isMacdonaldConjugator_of_hasPieriEigenfamily`, which needs a ring involution of
the coefficient field inverting both parameters. Such an involution exists at `𝕜`, where `q` and
`u` are indeterminates, but not at a general field even at an algebraically independent pair:
over `ℝ` the only ring endomorphism is the identity. `HJO.Ascent.commute_qop_ascend` then carries
the commutation of slope operators from `𝕜` to any `L`, through
`HJO.CollinearNarrowed.collinearCommutation_of_pfunPieriSupport`.

The other inputs of the route are theorems as well: the index shift is
`HJO.Bglx.exists_isIndexShift_param`, and the unnormalised Macdonald eigenbasis is
`HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_param`. -/
@[hjo "prop_challenge_collinear"]
theorem collinearCommutation_general (L : Type*) [Field L] [Algebra ℚ L] :
    External.CollinearCommutation L :=
  CollinearNarrowed.collinearCommutation_of_pfunPieriSupport Ascent.Kk
    (Standing.hasPfunPieriSupport_param Ascent.Kk) L

/-- **The collinear input at the standing instance**, which is the form the two theorems below
consume. `HJO.Debt.collinearCommutation_general` at `L = Base`. -/
theorem collinearCommutation : External.CollinearCommutation Base :=
  collinearCommutation_general Base

/-! ### The main results over the shuffle input

The endgame at the model (`HJO/Main/Final.lean`) takes `HJO.External.CollinearCommutation Base`
and `HJO.External.Shuffle Base`, and the first of those is `HJO.Debt.collinearCommutation`. So
the two theorems below state the main results over the shuffle input alone, taken as the `Prop`
itself rather than as any particular route to it. The `_of_debt` pair further down takes
`HJO.ShuffleAbove Base`, one route to that input. -/

/-- **The finite identity, over the quoted shuffle input alone.** The collinear input is discharged
by `HJO.Debt.collinearCommutation`; this takes the other one as stated, by whatever route proves
it. -/
theorem finiteSeries_eq_of_shuffle (hshuffle : External.Shuffle Base)
    {a b : ℕ} (hab : Nat.Coprime a b) (ha : 1 < a) (hb : a < b) (N : ℕ) :
    Gaps.finiteSeries a b N
      = qPochhammer PowerSeries.X PowerSeries.X N * HJO.Cylindric.boundedGF a b N :=
  open HJO.Final in by
  obtain ⟨Θ, hΘ⟩ := Witness.exists_isSlopeHom collinearCommutation hab ha hb
  exact Assembly.finiteSeries_eq_qPochhammer_mul_boundedGF ExternalDischarged.rankOneDinv
    GoodTraverseDischarged.goodTraverse CoercivityDischarged.huangCoercivity hshuffle
    (realise Base) (isRealisation_realise Base) hab ha hb
    (Witness.algebraicIndependent_param (algebraMap Witness.Coeff Base) Witness.algebraMap_injective
      _ algebraMap_qVar) (by rw [algebraMap_qVar]; exact hΘ) (isEvaluationHom_phi hΘ) N

/-- **The Huang--Jiang--Oblomkov conjecture, over the quoted shuffle input alone.** -/
theorem conjecture_of_shuffle (hshuffle : External.Shuffle Base)
    {a b : ℕ} (hab : Nat.Coprime a b) (ha : 1 < a) (hb : a < b) : HJO.Conjecture a b :=
  open HJO.Final in by
  obtain ⟨Θ, hΘ⟩ := Witness.exists_isSlopeHom collinearCommutation hab ha hb
  exact Assembly.conjecture ExternalDischarged.rankOneDinv GoodTraverseDischarged.goodTraverse
    CoercivityDischarged.huangCoercivity hshuffle
    (realise Base) (isRealisation_realise Base) hab ha hb
    (Witness.algebraicIndependent_param (algebraMap Witness.Coeff Base) Witness.algebraMap_injective
      _ algebraMap_qVar) (by rw [algebraMap_qVar]; exact hΘ) (isEvaluationHom_phi hΘ)
    CylindricProductDischarged.cylindricProduct

/-! #### Composing with the live route needs care: there is an instance diamond on `Base`

The natural convenience wrapper -- one taking `LhsComputes` and `MellitInduction` directly and
composing `HJO.Mellit.shuffle_of_lhs_and_induction` inside -- does NOT typecheck when its
hypotheses are restated in this file, and the reason is worth recording rather than worked around.
A binder written here as `∀ q u : Base, AlgebraicIndependent ℤ ![q, u] → …` resolves
`CommRing Base` through `OreLocalization.instCommRing` and `Algebra ℤ Base` through
`OreLocalization.instAlgebra`, while `HJO.Mellit.shuffle_of_lhs_and_induction` -- stated for a
general `L` with `[Field L] [Algebra ℚ L]` and then instantiated at `Base` -- carries
`(FractionRing.field Witness.Coeff).toCommRing` and `Ring.toIntAlgebra Base`. Those are the same
instances mathematically and different terms to the elaborator, so the application is rejected with
an `AlgebraicIndependent` type mismatch. It is the `Base` instance diamond this library has paid
for before.

So compose at the CALL SITE, where the hypotheses already carry the shape
`shuffle_of_lhs_and_induction` gave them:

`HJO.Debt.conjecture_of_shuffle (HJO.Mellit.shuffle_of_lhs_and_induction hlhs hind) hab ha hb` -/

/-- **The finite identity over `HJO.ShuffleAbove`**, the OTHER route to the quoted input -- the raw
above-diagonal expansion of Mellit's Section 6, with no reduction attached. Kept because it is
correct and because it records that the two routes are alternatives, not two debts. -/
theorem finiteSeries_eq_of_debt (habove : ShuffleAbove Base)
    {a b : ℕ} (hab : Nat.Coprime a b) (ha : 1 < a) (hb : a < b) (N : ℕ) :
    Gaps.finiteSeries a b N
      = qPochhammer PowerSeries.X PowerSeries.X N * HJO.Cylindric.boundedGF a b N :=
  finiteSeries_eq_of_shuffle (shuffle_of_shuffleAbove habove) hab ha hb N

/-- **The Huang--Jiang--Oblomkov conjecture over `HJO.ShuffleAbove`**, the other route. -/
theorem conjecture_of_debt (habove : ShuffleAbove Base)
    {a b : ℕ} (hab : Nat.Coprime a b) (ha : 1 < a) (hb : a < b) : HJO.Conjecture a b :=
  conjecture_of_shuffle (shuffle_of_shuffleAbove habove) hab ha hb

end HJO.Debt
