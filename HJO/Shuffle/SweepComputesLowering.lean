/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CharWordPartial
public import HJO.CarlssonMellit.MarkedWordChar
public import HJO.Shuffle.SweepWordTransport
public meta import HJO.Attr

/-! # The sweep leg rests on `HJO.Dyck.isLoweringSum` alone

`HJO.Mellit.SweepComputes` is one of exactly three hypotheses of the theorem
`HJO.Mellit.shuffle_of_three`, which concludes `HJO.External.Shuffle L` from those three and
nothing else. This file composes the chain that reduces it to a single obligation,
`HJO.Dyck.IsLoweringSum` — `HJO.Dyck.isLoweringSum`:

* `HJO.Mellit.sweepComputes` rests on `HJO.Mellit.map_constantCoeff_markedWordOp'` alone
  (`HJO.Mellit.sweepComputes_of_cor46_alone`);
* `HJO.Mellit.map_constantCoeff_markedWordOp'` rests on
  `HJO.Dyck.realisation_constantCoeff_markedWordOp'` alone
  (`HJO.Sweep.map_constantCoeff_markedWordOp_one_eq_pathMarkedCharSeries`), the conclusion at the
  empty marking being literally the hypothesis;
* `HJO.Dyck.realisation_constantCoeff_markedWordOp'` rests on `HJO.Dyck.isLoweringSum` alone
  (`HJO.Dyck.realisation_constantCoeff_markedWordOp`), as do `HJO.Dyck.isSigmaCharacter_dminusCM'`
  and `HJO.Dyck.mem_piece_and_isSigmaCharacter_partialWordOp'`.

So the composite below is `SweepComputes q u a b` from `IsLoweringSum q` and three conditions on
the parameter, and it is the exact statement of what remains to be proved on this leg.

## The three conditions on `q`, and why each is there

* `q ≠ 0` is what collecting the scalars of `HJO.Mellit.sweepOperator` costs: the type-`C` scalars
  `q^{-a}` and the type-`D` scalars `q^{a}` combine into the single power `q^{Σ_D - Σ_C}` by
  `zpow_add₀`, which is false at `q = 0`.
* `q ≠ 1` is what `HJO.Mellit.map_constantCoeff_markedWordOp'` costs at a nonempty marking: the pair
  factor `HJO.Sweep.cmCorner q k` is `(q - 1)⁻¹ • (…)`, so `Ξ_{π,T}` vanishes at `q = 1` while
  `χ(π, T)` does not. This is a defect of that lemma's Lean statement, not of the mathematics —
  the mathematics takes place over `𝕜 = ℚ(q, u)`, where `q` is an indeterminate.
* `∀ r, IsUnit (q ^ (r + 1) - 1)` is what
  `HJO.Dyck.auxZeroMap_eq_pathCharSeries_of_isSigmaCharacter` costs, through the bijectivity of `θ`.
  It does not imply `q ≠ 0`: at `q = 0` every `q ^ (r + 1) - 1` is `-1`.

All three hold in the coefficient field, and the consumer supplies the first:
`HJO.Mellit.ne_zero_of_algebraicIndependent_fst` derives `q ≠ 0` from the algebraic independence
`shuffle_of_three` asks for, and the same independence gives the other two.

## Main results

* `HJO.Mellit.sweepComputes_of_isLoweringSum`: `SweepComputes q u a b` from `IsLoweringSum q`.
* `HJO.Mellit.constantCoeff_sweepWord_one_mem_lambdaComp_and_map_eq_smul_sweepChar_of_isLoweringSum`
  : the same at one path, in the form `HJO.Mellit.sweepComputes` is stated in.

`IsLoweringSum` is open, so neither `HJO.Mellit.sweepComputes` nor any lemma of the chain is proved
unconditionally here; what is proved is that the whole leg reduces to that one statement.

## References

The lemmas `HJO.Mellit.sweepComputes`,
`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar`,
`HJO.Mellit.map_constantCoeff_markedWordOp'`, `HJO.Dyck.realisation_constantCoeff_markedWordOp'`,
`HJO.Dyck.mem_piece_and_isSigmaCharacter_partialWordOp'`, `HJO.Dyck.isSigmaCharacter_dminusCM'` and
`HJO.Dyck.isLoweringSum`; and E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J.
Amer. Math. Soc. **31** (2018) 661--697, Section 4 and the subsection "Lowering operator".
-/

@[expose] public section

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] [CharZero L] {a b N : ℕ}

/-- **`HJO.Mellit.map_constantCoeff_markedWordOp'` modulo `HJO.Dyck.isLoweringSum`.** The marked
word computes the marked characteristic series, with
`HJO.Dyck.realisation_constantCoeff_markedWordOp'` discharged by
`HJO.Dyck.realisation_constantCoeff_markedWordOp`: that theorem is this one at the empty marking, so
the two compose with no bridge. -/
theorem map_constantCoeff_markedWordOp_of_isLoweringSum (q : L) (hq0 : q ≠ 0) (hq1 : q ≠ 1)
    (hqu : ∀ r : ℕ, IsUnit (q ^ (r + 1) - 1)) (hsum : Dyck.IsLoweringSum q)
    {ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L} (hι : Sym.IsRealisation ι) {n : ℕ}
    (x : Fin n → ℕ) (T : Finset (ℕ × ℕ)) (hx : Dyck.IsSquareDyck n x) (hT : T ⊆ Dyck.corner x) :
    ι (MvPolynomial.constantCoeff (Sweep.markedWordOp q x T (1 : Total L)))
      = Dyck.pathMarkedCharSeries q x T :=
  Sweep.map_constantCoeff_markedWordOp_one_eq_pathMarkedCharSeries q hx hT hq1
    fun _ hy => Dyck.realisation_constantCoeff_markedWordOp q hq0 hqu hy hι hsum

/-- **`HJO.Mellit.sweepComputes` modulo `HJO.Dyck.isLoweringSum` alone**, in the form it is
stated in: for an above-diagonal `(aN, bN)`-path `y` and a realisation `ι`, the element
`f = W(P̂)(1)` of `Λ` is homogeneous of degree `bN` and
`ι(f) = u^{ârea(P̂)} q^{ĥ(P̂) - max t̂dinv(P̂)} χ(P̂)`. -/
theorem constantCoeff_sweepWord_one_mem_lambdaComp_and_map_eq_smul_sweepChar_of_isLoweringSum
    (q u : L) (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hqu : ∀ r : ℕ, IsUnit (q ^ (r + 1) - 1))
    (hsum : Dyck.IsLoweringSum q) {y : Heights a b N} (hy : IsAboveDiagonal y)
    {ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L} (hι : Sym.IsRealisation ι) :
    MvPolynomial.constantCoeff (sweepWord q u y (1 : Total L)) ∈ Sym.LambdaComp L (b * N) ∧
      ι (MvPolynomial.constantCoeff (sweepWord q u y (1 : Total L))) =
        (u ^ aboveArea y * q ^ ((aboveHookCount y : ℤ) - (aboveMaxTdinv y : ℤ))) •
          sweepChar q y :=
  constantCoeff_sweepWord_one_mem_lambdaComp_and_map_eq_smul_sweepChar_of_cor46_alone q u hq0 hy hι
    fun {_} x T _ hx hT =>
      map_constantCoeff_markedWordOp_of_isLoweringSum q hq0 hq1 hqu hsum hι x T hx hT

/-- **`HJO.Mellit.SweepComputes` from `HJO.Dyck.isLoweringSum` alone.** This is the whole of the
sweep leg of `HJO.Mellit.shuffle_of_three` reduced to one open statement: `HJO.Dyck.IsLoweringSum`,
the statement of `HJO.Dyck.isLoweringSum`, together with the three conditions on `q` recorded in the
module docstring, all of which hold over the coefficient field. -/
theorem sweepComputes_of_isLoweringSum (q u : L) (hq0 : q ≠ 0) (hq1 : q ≠ 1)
    (hqu : ∀ r : ℕ, IsUnit (q ^ (r + 1) - 1)) (hsum : Dyck.IsLoweringSum q) :
    SweepComputes q u a b :=
  sweepComputes_of_cor46_alone q u hq0 fun _ hι {_} x T _ hx hT =>
    map_constantCoeff_markedWordOp_of_isLoweringSum q hq0 hq1 hqu hsum hι x T hx hT

end HJO.Mellit
