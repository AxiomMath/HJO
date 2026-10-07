/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepWordValuesTwoThreeTwo

/-! # `HJO.Mellit.MellitInduction` at `(a,b) = (2,3)`, `N = 2`, `α = (1,1)`: decided

`HJO/Shuffle/SweepInductionInstanceTwo.lean` reduces the clause of
`HJO.Mellit.mellitInduction_sweepWitness` at this instance to one identity in `HJO.Sweep.Total L` —
the statement that the invariant of the `4 × 6` rectangle at the colouring `c_{(1,1)}` and the level
`9/2` equals
`qe_1^2y_1^2y_2^2 + q(q-1)e_2y_1^2y_2^2 - que_1(y_1^3y_2^2 + y_1^2y_2^3) + qu^2y_1^3y_2^3`. This
file evaluates that invariant and discharges the equivalence.

## The three steps

1. `HJO.Mellit.aboveReturnPaths_two_three_two_one_one`: the index set of `HJO.Mellit.dsc` at this
   colouring is the four paths `(0,2,3,5,6)`, `(0,2,3,6,6)`, `(0,3,3,5,6)`, `(0,3,3,6,6)`. Then
   `HJO.Mellit.dsc_compColouring_eq_sum_partialSweepWord` turns the sum over *traces*
   into a sum over those four paths with no multiplicity.
2. `HJO/Shuffle/SweepWordValuesTwoThreeTwo.lean` evaluates each of the four partial sweep words
   on the vacuum.
3. The four values add to the right-hand side, and the `e_1y_1^3y_2^2` coefficient is where two of
   them cancel: `(0,2,3,6,6)` contributes `q(q-1)u` and `(0,3,3,5,6)` contributes `-q^2u`, and the
   sum is `-qu`. Neither path alone gives the answer's coefficient.

## What this decides

`HJO.Mellit.mellitInduction_two_three_one_one` is the clause of `HJO.Mellit.MellitInduction` at
`(a,b) = (2,3)`, `N = 2`, `α = (1,1)` — both quantifiers, over replication families and over
admissible separating levels, in both directions — proved outright. It is the first instance of that
clause with `N > 1` to be decided, and the first at all where the left-hand side is a sum of more
than two sweep words.

## Genericity

`q ≠ 0`, `u ≠ 0` and `q ≠ 1`, and no more; `HJO.Mellit.two_three_two_in_range` derives all three
from the `AlgebraicIndependent ℤ ![q, u]` that `HJO.Mellit.MellitInput` carries, so
`HJO.Mellit.mellitInduction_two_three_one_one_of_input` assumes nothing beyond that hypothesis.
Each of the three is the inverse-becomes-zero hazard and not bookkeeping: at `q = 0` or `u = 0` the
letter `(qu)^{-1}z_1` of `HJO.Sweep.slopeOperator` is the zero map, at `q = 1` the scalar
`q^2/(1-q)` of `HJO.Sweep.zop` is undefined, and `HJO.Sweep.corner` divides by `q - 1`; a verdict at
any of them would be false rather than vacuous. `(2,3)` is coprime with `1 < 2 < 3`, so the instance
is strictly inside `MellitInput`'s quantification and is not the degenerate `a = 1` case.

## References

This file concerns `HJO.Mellit.mellitInduction_sweepWitness`, `HJO.Mellit.dsc`,
`HJO.Mellit.compColouring`, `HJO.Mellit.sweepOperator`, `HJO.Mellit.stage`.
-/

@[expose] public section

namespace HJO.Mellit

open Finset HJO.Paths HJO.Sweep HJO.Sym

/-- **The index set of the `α = (1,1)` sum at `(a,b) = (2,3)`, `N = 2`**: the four paths
`(0,2,3,5,6)`, `(0,2,3,6,6)`, `(0,3,3,5,6)`, `(0,3,3,6,6)`, and no others.

This is `HJO.Mellit.filter_aboveDiagonal_compColouring_two_three_one_one` read through the return
composition rather than the colouring: `HJO.Mellit.aboveReturnPaths` is what
`HJO.Mellit.dsc_compColouring_eq_sum_partialSweepWord` sums over, and
`HJO.Mellit.colouring_eq_compColouring_iff` says the two descriptions agree on an above-diagonal
path at an admissible separating level.

Deriving it rather than deciding it is not a stylistic choice: the whole `Finset` equality does not
reduce in the module system, the `Fintype` instance on `HJO.Paths.Heights 2 3 2` getting stuck on
`Multiset.Pi.cons`. The equality is obtained instead from four individual membership checks against
a counting lemma, and this reuses it. -/
theorem aboveReturnPaths_two_three_two_one_one :
    aboveReturnPaths 2 3 2 [1, 1]
      = {baseTwoThreeTwoA, baseTwoThreeTwoB, baseTwoThreeTwoC, baseTwoThreeTwoD} := by
  have hiff : ∀ y : Paths.Heights 2 3 2, Paths.IsAboveDiagonal y →
      (colouring y (sepLevel 2 2) = compColouring 2 3 [1, 1] ↔ Paths.HasAboveReturns [1, 1] y) :=
    fun y hy => colouring_eq_compColouring_iff (isAdmissibleLevel_sepLevel 2 2)
      (separatesDiagonal_sepLevel' 2 3 2) (by decide) (by omega) (by omega) (by simp) rfl hy
  rw [← filter_aboveDiagonal_compColouring_two_three_one_one]
  ext y
  rw [mem_aboveReturnPaths_iff, Finset.mem_filter]
  refine ⟨fun h => ⟨Finset.mem_univ y, h.1, (hiff y h.1).2 h⟩,
    fun h => (hiff y h.2.1).1 h.2.2⟩

section Value

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- **`D_{9/2,c_{(1,1)}} = qe_1^2y_1^2y_2^2 + q(q-1)e_2y_1^2y_2^2 - que_1(y_1^3y_2^2 + y_1^2y_2^3)
+ qu^2y_1^3y_2^3` in the `4 × 6` rectangle**, for `q ∉ {0,1}`.

The sum of the four words of `HJO.Mellit.aboveReturnPaths_two_three_two_one_one`. Two of the four
cancel against each other on `e_1y_1^3y_2^2`: `(0,2,3,6,6)` gives `q(q-1)u` there and `(0,3,3,5,6)`
gives `-q^2u`, adding to `-qu`. So no single path carries the answer's coefficient and the collapse
is genuine rather than a bookkeeping artefact. -/
theorem dsc_two_three_two_one_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    dsc q u 2 3 2 (sepLevel 2 2) (compColouring 2 3 [1, 1])
      = q • (MvPolynomial.C (elemSymm L 1 * elemSymm L 1)
            * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2))
        + (q * (q - 1)) • (MvPolynomial.C (elemSymm L 2)
            * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2))
        - (q * u) • (MvPolynomial.C (elemSymm L 1)
            * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2))
        - (q * u) • (MvPolynomial.C (elemSymm L 1)
            * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3))
        + (q * u ^ 2) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3) := by
  have hAB : baseTwoThreeTwoA ≠ baseTwoThreeTwoB := by decide
  have hAC : baseTwoThreeTwoA ≠ baseTwoThreeTwoC := by decide
  have hAD : baseTwoThreeTwoA ≠ baseTwoThreeTwoD := by decide
  have hBC : baseTwoThreeTwoB ≠ baseTwoThreeTwoC := by decide
  have hBD : baseTwoThreeTwoB ≠ baseTwoThreeTwoD := by decide
  have hCD : baseTwoThreeTwoC ≠ baseTwoThreeTwoD := by decide
  rw [dsc_compColouring_eq_sum_partialSweepWord q u (isAdmissibleLevel_sepLevel 2 2)
      (separatesDiagonal_sepLevel' 2 3 2) (by decide) (by omega) (by omega) (by simp) rfl,
    aboveReturnPaths_two_three_two_one_one,
    Finset.sum_insert (by simp [hAB, hAC, hAD]), Finset.sum_insert (by simp [hBC, hBD]),
    Finset.sum_insert (by simp [hCD]), Finset.sum_singleton,
    partialSweepWord_baseTwoThreeTwoA_apply_one hq0 hq1,
    partialSweepWord_baseTwoThreeTwoB_apply_one hq0 hq1,
    partialSweepWord_baseTwoThreeTwoC_apply_one hq0 hq1,
    partialSweepWord_baseTwoThreeTwoD_apply_one hq0 hq1]
  simp only [← scal_mul_eq_smul_total]
  simp only [scal_eq_algebraMap, map_sub, map_mul, map_one, map_pow]
  ring

/-! ### The clause, decided -/

/-- **The clause of `HJO.Mellit.mellitInduction_sweepWitness` at `(a,b) = (2,3)`, `N = 2`,
`α = (1,1)`, proved.**

Both quantifiers of `HJO.Mellit.MellitInduction`'s body are discharged — over replication families
and over admissible separating levels — because
`HJO.Mellit.mellitInduction_two_three_one_one_iff_dsc` removes them in both directions, and what it
leaves is the evaluation `HJO.Mellit.dsc_two_three_two_one_one`.

`q ≠ 0`, `u ≠ 0`, `q ≠ 1`: see the module docstring on why none of the three is removable. -/
theorem mellitInduction_two_three_one_one (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    ∀ Ω, IsReplicationFamily (sweepWitness q u 2 3) Ω →
      ∀ η : ℚ, IsAdmissibleLevel η → SeparatesDiagonal 2 3 2 η →
        (sweepWitness q u 2 3).D η (compColouring 2 3 [1, 1])
          = ((-1 : L) ^ ((2 - 1) * 2)
              * (q * u) ^ ((([1, 1] : List ℕ).length : ℤ) - ((2 : ℕ) : ℤ))) •
              stageWord (sweepWitness q u 2 3) Ω 2 3 [1, 1] :=
  (mellitInduction_two_three_one_one_iff_dsc hq0 hu0 hq1).2
    (dsc_two_three_two_one_one hq0 hq1)

/-- **The clause at this instance, from `HJO.Mellit.MellitInput`'s own hypothesis alone.** The three
parameter exclusions are *derived* from `AlgebraicIndependent ℤ ![q, u]` by
`HJO.Mellit.two_three_two_in_range`, so nothing is assumed of `q` and `u` beyond what
`HJO.Mellit.MellitInput` carries. This is the check against a verdict at `q = 1` or `u = 0`, each
of which lies outside the quantification and at each of which a letter of
`HJO.Sweep.slopeOperator` or `HJO.Sweep.zop` degenerates to the zero map. -/
theorem mellitInduction_two_three_one_one_of_input (hqu : AlgebraicIndependent ℤ ![q, u]) :
    ∀ Ω, IsReplicationFamily (sweepWitness q u 2 3) Ω →
      ∀ η : ℚ, IsAdmissibleLevel η → SeparatesDiagonal 2 3 2 η →
        (sweepWitness q u 2 3).D η (compColouring 2 3 [1, 1])
          = ((-1 : L) ^ ((2 - 1) * 2)
              * (q * u) ^ ((([1, 1] : List ℕ).length : ℤ) - ((2 : ℕ) : ℤ))) •
              stageWord (sweepWitness q u 2 3) Ω 2 3 [1, 1] :=
  have h := two_three_two_in_range hqu
  mellitInduction_two_three_one_one h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2

/-- **The clause at this instance is not vacuous.** A replication family exists and `9/2` is an
admissible separating level, so `HJO.Mellit.mellitInduction_two_three_one_one` asserts an identity
that is actually made — the trap that every statement of the Mellit layer
opens "let `Ω` be a replication family" and would be vacuously true with none exhibited. -/
theorem mellitInduction_two_three_one_one_nonvacuous (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    ∃ Ω, IsReplicationFamily (sweepWitness q u 2 3) Ω ∧
      IsAdmissibleLevel (sepLevel 2 2) ∧ SeparatesDiagonal 2 3 2 (sepLevel 2 2) ∧
        (sweepWitness q u 2 3).D (sepLevel 2 2) (compColouring 2 3 [1, 1])
          = ((-1 : L) ^ ((2 - 1) * 2)
              * (q * u) ^ ((([1, 1] : List ℕ).length : ℤ) - ((2 : ℕ) : ℤ))) •
              stageWord (sweepWitness q u 2 3) Ω 2 3 [1, 1] := by
  obtain ⟨Ω, hΩ⟩ := exists_isReplicationFamily (sweepWitness q u 2 3)
  exact ⟨Ω, hΩ, isAdmissibleLevel_sepLevel 2 2, separatesDiagonal_sepLevel' 2 3 2,
    mellitInduction_two_three_one_one hq0 hu0 hq1 Ω hΩ (sepLevel 2 2)
      (isAdmissibleLevel_sepLevel 2 2) (separatesDiagonal_sepLevel' 2 3 2)⟩

end Value

end HJO.Mellit

end
