/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.PfunSupportDischarge
public import HJO.Macdonald.PieriSupportFull
public meta import HJO.Attr

/-! # The collinear commutation input is not an assumption

`HJO/Defs.lean` states the results this library quotes from the literature as
`Prop`-valued assumptions, so that every consumer carries what it depends on and no quoted result
is used silently. `HJO/Discharged/` records the proofs, so that "the assumption is dischargeable" is
a compiled fact rather than a claim.

This file does that for `HJO.External.CollinearCommutation`, which is discharged outright at
every characteristic-zero field.

**Why it is a file of its own rather than a section of
`HJO/Discharged/External.lean`,** which is where a reader would look first: that
module is *upstream* of this mathematics. `HJO/Evaluation/PhiPoly.lean` and
`HJO/Evaluation/PhiE.lean` both import it, and the collinear files import them, so
`ExternalDischarged` importing `HJO.Collinear.*` is an import cycle and Lean rejects it. The naming
follows the siblings (`CoercivityDischarged`, `CylindricProductDischarged`,
`GoodTraverseDischarged`), which are one file per discharged input for the same reason.

## Main results

* `HJO.CollinearDischarged.collinearCommutation`: `HJO.External.CollinearCommutation L` for every
  field `L` of characteristic zero, with no hypotheses.

## What does NOT establish this, and why searching can mislead

* `HJO.CollinearNarrowed.CollinearCommute` is the narrowing vocabulary in
  `HJO/Evaluation/CollinearNarrowed.lean`, not this theorem: a `Prop`-valued definition, which says
  nothing about whether the assumption is discharged.
* `HJO.CollinearNarrowed.collinearCommutation` still takes `CollinearCommute L` as a hypothesis.
  It is not the discharge.

The theorem below, and `#print axioms` on it, are what settle the question.

## References

`HJO.Standing.hasPfunPieriSupport_param` is the input that closes the collinear side of the
Rogers--Ramanujan chain.
-/

@[expose] public section

namespace HJO.CollinearDischarged

/-- **`HJO.External.CollinearCommutation` is a theorem, not an assumption**, at every field of
characteristic zero and with no hypotheses whatever.

Two results compose to it: `HJO.Standing.hasPfunPieriSupport_param` proves
`HJO.Sym.HasPfunPieriSupport` at the parameter field with no hypothesis, and
`HJO.CollinearNarrowed.collinearCommutation_of_pfunPieriSupport` carries it to the assumption at an
arbitrary `L`.

`#print axioms` on this declaration gives exactly `[propext, Classical.choice, Quot.sound]`: no
`sorryAx`, and nothing quoted from the literature. -/
theorem collinearCommutation (L : Type*) [Field L] [Algebra ℚ L] :
    HJO.External.CollinearCommutation L :=
  HJO.CollinearNarrowed.collinearCommutation_of_pfunPieriSupport HJO.Ascent.Kk
    (HJO.Standing.hasPfunPieriSupport_param HJO.Ascent.Kk) L

/- The same input at the standing field of the main proof -- the form
`HJO.Debt.conjecture_of_debt` consumes -- is `HJO.Debt.collinearCommutation`, which is this theorem
applied to `HJO.PhiMul.Witness.Base`. It is not restated here: `Base` lives downstream of
`HJO/Evaluation/PhiPoly.lean`, which imports `HJO/Discharged/External.lean`, and pulling
that chain in for a one-line specialisation would risk the import cycle described in the module
docstring. -/

/-! ### The shuffle input

`HJO.External.Shuffle` is discharged too, at every field of characteristic zero, by
`HJO.Ascent.shuffle` in `HJO/Shuffle/ShuffleClosed.lean`. It is not restated here for the
same reason as above: that module sits far downstream of this one. With both inputs proved, the
main theorems hold with no hypothesis, as `HJO.conjecture` and
`HJO.finiteSeries_eq_qPochhammer_mul_boundedGF` in `HJO/Main.lean`.
-/

end HJO.CollinearDischarged

/-! ### The same discharge in operator form, without the narrowing `1 < a < b`

`HJO.External.CollinearCommutation` and `HJO.CollinearNarrowed.CollinearCommute` both quantify only
over `1 < a < b`, that being the range their consumers in this library read, so neither of them
states the commutation at the diagonal pair `(1, 1)` or at a pair with `a > b`. The Euclidean
descent underneath, `HJO.Sym.collinear_commute_of_diag`, needs only `0 < a` and `0 < b`, and
`HJO.CollinearNarrowed.commute_qop_param` is already stated at that range: the narrowing happens in
`collinearCommute_of_pieri_param`, whose proof spends `1 < a` and `a < b` on nothing but `omega` to
`0 < a` and `0 < b`. The theorem below is that proof with the narrowing not imposed.
-/

namespace HJO.Ascent

open HJO.Sym HJO.Standing HJO.CollinearNarrowed

/-- **Collinear commutativity at algebraically independent parameters.** Let `L` be a field
containing `ℚ` and let `x, y ∈ L` satisfy no nonzero polynomial relation over `ℤ`. Then for every
coprime pair `(a, b)` with `a, b ≥ 1` and all `k, l ≥ 1`, the slope operators `Q_{ak, bk}` and
`Q_{al, bl}` at the instance `(L, x, y)` commute.

This is `HJO.CollinearNarrowed.CollinearCommute L` with its restriction to `1 < a < b` dropped, and
it has no hypotheses beyond the genericity of the pair: the Macdonald chain the descent runs on is
discharged at the standing field by `HJO.Standing.hasPfunPieriSupport_param`, exactly as in
`HJO.CollinearDischarged.collinearCommutation`.

The descent runs at `𝕜`, where the parameter inversions the Macdonald conjugator needs exist
(`HJO.CollinearNarrowed.commute_qop_param`), and `HJO.Ascent.commute_qop_ascend` carries the
resulting commutation to `L` along the embedding of `𝕜` determined by the algebraically independent
pair -- the ascent's "a pair intertwined with a commuting pair commutes", which is
`HJO.Ascent.commute_of_intertwined`. The index order is converted because the descent produces
`(k * a, k * b)` while `CollinearCommute` asks for `(a * k, b * k)`. -/
@[hjo "lem_asc_collinear_commute"]
theorem commute_qop_of_algebraicIndependent {L : Type*} [Field L] [Algebra ℚ L] {x y : L}
    (h : AlgebraicIndependent ℤ ![x, y]) {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a)
    (hb : 0 < b) {k l : ℕ} (hk : 0 < k) (hl : 0 < l) :
    Commute (Qop x y (a * k) (b * k)) (Qop x y (a * l) (b * l)) := by
  have hstd := commute_qop_param Kk
    (hasPieriEigenfamily_param Kk (hasPfunPieriSupport_param Kk)) hab ha hb hk hl
  have hasc := commute_qop_ascend Kk h hstd
  rwa [Nat.mul_comm k a, Nat.mul_comm k b, Nat.mul_comm l a, Nat.mul_comm l b] at hasc

end HJO.Ascent
