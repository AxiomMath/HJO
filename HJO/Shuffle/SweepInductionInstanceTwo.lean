/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepInductionInstance
public import HJO.Shuffle.SweepAppendTwoThree
public import HJO.Shuffle.MellitTwoPartTwoThree
public import HJO.Shuffle.SweepWitnessLhsSingleton
public import HJO.Shuffle.SweepWitnessBraid
public import HJO.Shuffle.MellitLevelRaise
public import HJO.Macdonald.StandingFacts

/-! # `HJO.Mellit.MellitInduction` at `(a,b) = (2,3)`, `N = 2`: the two instances, reduced

`HJO.Mellit.MellitInduction` (`HJO/Shuffle/Mellit.lean`) asserts
`D_{η,c_α} = (-1)^{(a-1)N}(qu)^{ℓ-N} G_{ℓ,α_ℓ} ⋯ G_{1,α_1}(1)` for every replication family, every
admissible separating level and every composition of `N` with positive parts.
`HJO/Shuffle/SweepInductionInstance.lean` decides it at `N = 1`, `α = (1)`, where both sides
are `e_1y_1^2 - uy_1^3`. This file takes the two instances at `N = 2` — the compositions `(1,1)`
and `(2)` of `2` — as far as the operator evaluations available here reach.

## What is reduced, and to what

`HJO.Mellit.mellitInduction_two_three_two_iff` removes **both** quantifiers of the clause at
`N = 2`, in both directions and at either composition: the replication family, because at this
witness the stage word does not depend on which family is taken and one is exhibited; and the level,
because the invariant does not depend on which admissible separating level is taken and `9/2` is
one. What is left in each case is a single identity in `HJO.Sweep.Total L` about `HJO.Mellit.dsc`:

* **`α = (1,1)`** (`HJO.Mellit.mellitInduction_two_three_one_one_iff_dsc`). Here `ℓ = N`, so the
  clause's scalar is `(-1)^2(qu)^0 = 1` and the right-hand side is evaluated outright:
  `HJO.Sweep.stageWordTotal_two_three_one_one` is `G_{2,1}G_{1,1}(1) = q·e_1^2y_1^2y_2^2 +
  q(q-1)·e_2y_1^2y_2^2 − qu·e_1(y_1^3y_2^2 + y_1^2y_2^3) + qu^2·y_1^3y_2^3`, with every sweep
  operator discharged. So the clause at this instance **is** the statement that the invariant of the
  `4 × 6` rectangle at `c_{(1,1)}` is that polynomial.
* **`α = (2)`** (`HJO.Mellit.mellitInduction_two_three_two_iff_dsc`). This is the first instance
  with `ℓ < N`, where `(qu)^{ℓ-N}` is a genuine inverse power. The right-hand side is not evaluated
  but *rewritten*: the stage word at a one-part composition with `A = 2` is one replicated letter on
  the stage word at `A = 1` (`HJO.Sweep.stageTotal_two_eq`), and that is the `N = 1` seed already
  evaluated. So the clause reads `D_{9/2,c_{(2)}} = -(qu)^{-1}Z^{(1)}_{2,3}(D_{5/2,c_{(1)}})`
  (`HJO.Sweep.stageWordTotal_two_three_two_eq_replicated_neg_dsc`) — the first `ℓ < N` instance is a
  statement about `HJO.Mellit.dsc` at two rectangles and one explicit operator, with no stage
  word, no replication family and no level in it.

**The inverse power is not an obstruction.** The `(qu)^{-1}` the clause carries at `α = (2)` is
exactly the inverse `Z^{(1)}_{2,3}` carries through `HJO.Sweep.slopeOperator`'s `(qu)^{-1}z_1`,
and the two cancel: the reduced identity above has no inverse power in it. This is what the `ℓ < N`
factor does at this instance, and it does not degenerate anywhere `q ≠ 0`, `u ≠ 0`, `q ≠ 1` holds.

## What deciding the two instances takes

**Both instances are decided, though not in this file.** `α = (1,1)` is
`HJO.Mellit.mellitInduction_two_three_one_one`
(`HJO/Shuffle/SweepInductionInstanceTwoDecided.lean`) and `α = (2)`, the first instance with
`ℓ < N`, is `HJO.Mellit.mellitInduction_two_three_alphaTwo`
(`HJO/Shuffle/SweepInductionInstanceTwoAlphaDecided.lean`), both depending on exactly the axioms
`[propext, Classical.choice, Quot.sound]` and both discharged through the `iff`s below, so neither
can have drifted from the clause. The rest of this section describes what deciding them requires.

What both reductions leave is the left-hand side, and the left-hand side is a sum of sweep words:

* at `α = (1,1)`, four of them — `HJO.Mellit.filter_aboveDiagonal_compColouring_two_three_one_one`
  names the four above-diagonal paths, `(0,2,3,5,6)`, `(0,2,3,6,6)`, `(0,3,3,5,6)`, `(0,3,3,6,6)`,
  and `HJO.Mellit.card_traceIndex_two_three_one_one` says the sum of `HJO.Mellit.dsc` over traces
  has four terms, so nothing collapses;
* at `α = (2)`, nineteen — `HJO.Mellit.card_traceIndex_two_three_two`, which counts the *traces* the
  nineteen paths of `HJO.Mellit.card_aboveDiagonal_compColouring_two_three_two` realize and again
  finds no collapse.

Those words are products of eight to sixteen event operators of `HJO.Mellit.sweepOperator` read at
widths reaching `4`, so evaluating them needs `d_+`, `d_-` and `Δ` on `V_3` and `V_4`. The `N = 1`
instance needed those operators only on `V_1` and `V_2`, which is where the evaluation lemmas used
there stop: `HJO.Sweep.dplus_zero_one`, `HJO.Sweep.corner_one_auxVar_pow`,
`HJO.Mellit.dminus_two_X_zero_sq_mul_X_one` and their siblings are all at widths `0`, `1` and `2`.
That gap — the displacement of `e_3` and `e_4` under `τ_{k,k}` and the corner operator at widths `3`
and `4` — is the whole of what these two instances need beyond this file, and it is a gap in the
operator evaluations and not a difficulty about either instance.

Outside Lean both instances **compute out true**, by an independent symbolic evaluation of the same
definitions validated against three values proved in Lean
(`HJO.Mellit.dsc_two_three_one`, `HJO.Mellit.dsc_one_two_two` — itself an `N = 2` evaluation — and
`HJO.Sweep.stageTotal_two_three_zero_one_one`). That is evidence for the witness and not a proof of
it: nothing in this file rests on it, and the two equivalences above are exactly what a Lean proof
would have to discharge.

## Genericity

`q ≠ 0`, `u ≠ 0` and `q ≠ 1`, and no more; `HJO.Mellit.two_three_two_in_range` derives all three
from `AlgebraicIndependent ℤ ![q, u]`, the hypothesis `HJO.Mellit.MellitInput` is stated at, and
checks the three range conditions on `(a,b) = (2,3)` by `decide`. Each of the three is the
inverse-becomes-zero hazard rather than bookkeeping: at `q = 0` or `u = 0` the letter `(qu)^{-1}z_1`
of `HJO.Sweep.slopeOperator` is the zero map and at `q = 1` the scalar `q^2/(1-q)` of
`HJO.Sweep.zop` is undefined, so a clause asserting either value there would be false rather than
vacuous.

## References

The file is about the clause `HJO.Mellit.mellitInduction_sweepWitness`, read through
`HJO.Mellit.stage`, `HJO.Mellit.replicatedLetter`, `HJO.Sweep.slopeOperator`, `HJO.Sweep.zop`,
`HJO.Mellit.dsc`, `HJO.Mellit.compColouring` and `HJO.Mellit.sweepOperator`.
-/

@[expose] public section

namespace HJO.Sweep

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### A braid letter on a symmetric vector -/

omit [Algebra ℚ L] in
private theorem divDiffOne {F G : Total L}
    (h : ((auxVar 2 : Total L) - auxVar 1) * G = F - swapAux L 1 F) :
    dividedDiff 1 F = G :=
  (dividedDiff_unique (i := 1) le_rfl (by
    rw [show (MvPolynomial.X 1 - MvPolynomial.X (1 - 1) : Total L)
        = (auxVar 2 : Total L) - auxVar 1 from rfl]
    exact h)).symm

omit [Algebra ℚ L] in
/-- **`T_1` fixes a vector symmetric in `y_1, y_2`.** -/
theorem braidEnd_one_of_swapAux_eq (q : L) {F : Total L} (h : swapAux L 1 F = F) :
    braidEnd q 1 F = F := by
  have hdd : dividedDiff 1 F = 0 := divDiffOne (by rw [h]; ring)
  rw [braidEnd_apply', h, hdd, mul_zero, add_zero]

/-! ### The vector the two-part stage word is the braid image of -/

/-- The five-monomial vector of `V_2` that the two-part stage word at `(a,b) = (2,3)` is
`(qu)^{-1}q^2/(1-q)` times. -/
noncomputable def seedValueTwo (q u : L) : Total L :=
  (-((q - 1) * u)) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2
      * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
    + (-((q - 1) ^ 2 * u)) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2
        * MvPolynomial.C (elemSymm L 2))
    + ((q - 1) * u ^ 2) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2
        * MvPolynomial.C (elemSymm L 1))
    + ((q - 1) * u ^ 2) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3
        * MvPolynomial.C (elemSymm L 1))
    + (-((q - 1) * u ^ 3)) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3
        * MvPolynomial.C (1 : Lambda L))

/-- **`HJO.Sweep.seedValueTwo` is symmetric in `y_1` and `y_2`.** -/
theorem swapAux_seedValueTwo (q u : L) : swapAux L 1 (seedValueTwo q u) = seedValueTwo q u := by
  rw [seedValueTwo]
  simp only [← scal_mul_eq_smul_total, map_add, map_mul, map_pow, swapAux_scal, swapAux_C,
    swapAux_one_auxVar_one, swapAux_one_auxVar_two]
  ring

/-- **The slope operator's argument at `α = (1,1)`, evaluated.** The `z` letter of
`HJO.Sweep.slopeOperator` read on the train image of the seed: the two displacement defects of
`HJO.Sweep.zDefect` at `n = 2` supply the five monomials. This is
`HJO.Sweep.constantCoeff_lowerRun_two_auxVar_one_mul_zCommTwo_seedArgTwo` before the two lowerings,
so nothing is extracted and the value stays in `V_2`. -/
theorem auxVar_one_mul_zCommTwo_braidInvEnd_seedArgTwo (hq0 : q ≠ 0) :
    (auxVar 1 : Total L)
        * zCommTwo q u (braidInvEnd q 1 (-((auxVar 1 : Total L) * seedArgTwo q u)))
      = seedValueTwo q u := by
  have hz : zCommTwo q u (braidInvEnd q 1 (-((auxVar 1 : Total L) * seedArgTwo q u)))
      = -((auxVar 2 : Total L) ^ 2 * zDefect q u 2 (elemSymm L 1))
        + u • ((auxVar 2 : Total L) ^ 3 * zDefect q u 2 (1 : Lambda L)) := by
    rw [braidInvEnd_one_neg_auxVar_one_mul_seedArgTwo hq0,
      show ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
        = MvPolynomial.C (1 : Lambda L) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2) from
        by rw [MvPolynomial.C_1, one_mul],
      map_add, map_neg, map_smul, zCommTwo_monomial', zCommTwo_monomial']
  rw [hz, zDefect_two_elemSymm_one, zDefect_two_one, seedValueTwo]
  simp only [← scal_mul_eq_smul_total, scal, map_mul, map_sub, map_neg, map_one, map_pow]
  ring

/-! ### The two-part stage word at `(a,b) = (2,3)`, in closed form -/

/-- **`G_{2,1}G_{1,1}(1) = q·e_1^2y_1^2y_2^2 + q(q-1)·e_2y_1^2y_2^2 − qu·e_1(y_1^3y_2^2 +
y_1^2y_2^3) + qu^2·y_1^3y_2^3`**, the right-hand side of `HJO.Mellit.mellitInduction_sweepWitness`
at `(a,b) = (2,3)`, `N = 2`, `α = (1,1)`, with every sweep operator discharged.

Three things happen and none is bookkeeping. The stage at `A = 1` carries no replicated letter
(`HJO.Sweep.stageTotal_one_apply`), so the word is the descending train after the slope operator;
the descending train from the grading `2` is the single braid letter `T_1`
(`HJO.Sweep.trainDownEnd_two_one`), and that letter acts as the **identity**, because the vector it
meets is symmetric in `y_1` and `y_2` (`HJO.Sweep.swapAux_seedValueTwo`) — which is why this value
and `HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_two_three`, where the same
letter is killed by `d_-d_-` instead, carry the same coefficients. The scalar is where the two
inverses of the slope word, `(qu)^{-1}` from `HJO.Sweep.slopeOperator` and `q^2/(1-q)` from
`HJO.Sweep.zop`, are cancelled against the `(q-1)u` of the displacement defect.

`q ≠ 0`, `u ≠ 0`, `q ≠ 1` and nothing else, and all three are the inverse-becomes-zero hazard: at
`q = 0` or `u = 0` the letter `(qu)^{-1}z_1` is the zero map, at `q = 1` the scalar `q^2/(1-q)` of
`HJO.Sweep.zop` is undefined and `z_1` degenerates. At each the right-hand side genuinely collapses,
so a clause asserting this value there would be false, not vacuous. -/
theorem stageWordTotal_two_three_one_one (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    Mellit.stageWordTotal q u 2 3 [1, 1]
      = q • (MvPolynomial.C (elemSymm L 1 * elemSymm L 1)
            * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2))
        + (q * (q - 1)) • (MvPolynomial.C (elemSymm L 2)
            * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2))
        - (q * u) • (MvPolynomial.C (elemSymm L 1)
            * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2))
        - (q * u) • (MvPolynomial.C (elemSymm L 1)
            * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3))
        + (q * u ^ 2) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  have hqu : q * u ≠ 0 := mul_ne_zero hq0 hu0
  rw [stageWordTotal_one_one, stageTotal_one_apply, show (1 : ℕ) + 1 = 2 from rfl,
    trainDownEnd_two_one, neg_auxVar_one_mul_dplusStar_one_stageTotal hq0 hu0 hq1,
    slopeOperator_two_three_apply, map_neg, map_smul,
    auxVar_one_mul_zCommTwo_braidInvEnd_seedArgTwo (u := u) hq0,
    braidEnd_one_of_swapAux_eq q (swapAux_seedValueTwo q u),
    show ((-1 : L) ^ (2 - 1)) = -1 from by norm_num, seedValueTwo]
  simp only [neg_smul, smul_add, smul_neg, smul_smul]
  rw [show ((q * u)⁻¹ * (q ^ 2 / (1 - q))) * ((q - 1) * u) = -q from by field_simp; ring,
    show ((q * u)⁻¹ * (q ^ 2 / (1 - q))) * ((q - 1) ^ 2 * u) = -(q * (q - 1)) from by
      field_simp; ring,
    show ((q * u)⁻¹ * (q ^ 2 / (1 - q))) * ((q - 1) * u ^ 2) = -(q * u) from by field_simp; ring,
    show ((q * u)⁻¹ * (q ^ 2 / (1 - q))) * ((q - 1) * u ^ 3) = -(q * u ^ 2) from by
      field_simp; ring,
    MvPolynomial.C_1, mul_one]
  simp only [← scal_mul_eq_smul_total]
  ring_nf

/-! ### The one-part stage at `A = 2`: one replicated letter on the `A = 1` stage -/

/-- **`G_{k+1,2} = Z^{(k+1)}_{a,b}G_{k+1,1}`.** The stage of `HJO.Mellit.stage` at `A = 2` is the
stage at `A = 1` with one replicated letter in front, the power `A - 1` being `1` rather than `0`.
Unconditional, at every `(a,b)` and every grading. -/
theorem stageTotal_two_eq (q u : L) (a b k : ℕ) :
    Mellit.stageTotal q u a b k 2
      = Mellit.replicatedTotal q u a b k * Mellit.stageTotal q u a b k 1 := by
  rw [Mellit.stageTotal, Mellit.stageTotal]
  norm_num

/-- **The one-part stage word at `(a,b) = (2,3)`, `α = (2)`: one replicated letter on the
`N = 1` seed.** `Z^{(1)}_{2,3}` of `HJO.Sweep.stageTotal_two_three_zero_one_one`. This is the whole
of the right-hand side of `HJO.Mellit.mellitInduction_sweepWitness` at `N = 2`, `α = (2)` — the
first instance with `ℓ < N` — and it carries no sweep operator that the `N = 1` case did not already
discharge. -/
theorem stageWordTotal_two_three_two (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    Mellit.stageWordTotal q u 2 3 [2]
      = Mellit.replicatedTotal q u 2 3 0
          (-(MvPolynomial.C (elemSymm L 1) * (auxVar 1 : Total L) ^ 2)
            + u • (auxVar 1 : Total L) ^ 3) := by
  rw [Mellit.stageWordTotal_singleton, stageTotal_two_eq, Module.End.mul_apply,
    stageTotal_two_three_zero_one_one hq0 hu0 hq1]

/-- **The `α = (2)` stage word is one replicated letter on minus the `N = 1` invariant.**
`HJO.Mellit.dsc_two_three_one` is `D_{5/2,c_{(1)}} = e_1y_1^2 - uy_1^3` in the `2 × 3` rectangle and
the seed of `HJO.Sweep.stageWordTotal_two_three_two` is its negative, so the right-hand side of the
clause at `N = 2`, `α = (2)` is `Z^{(1)}_{2,3}` applied to `-D_{5/2,c_{(1)}}`.

This is the shape in which the first `ℓ < N` instance reduces to the decided `N = 1` one: the whole
of the stage word is gone, and what is left is one explicit operator applied to one known value. -/
theorem stageWordTotal_two_three_two_eq_replicated_neg_dsc (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) :
    Mellit.stageWordTotal q u 2 3 [2]
      = Mellit.replicatedTotal q u 2 3 0
          (-(Mellit.dsc q u 2 3 1 (Mellit.sepLevel 2 1) (Mellit.compColouring 2 3 [1]))) := by
  rw [stageWordTotal_two_three_two hq0 hu0 hq1, Mellit.dsc_two_three_one q u hq0 hq1]
  congr 1
  rw [← scal_mul_eq_smul_total, show (auxVar 1 : Total L) = MvPolynomial.X 0 from rfl]
  ring

end HJO.Sweep

namespace HJO.Mellit

open Finset HJO.Sym HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The left-hand side at `N = 2`, off the level -/

/-- **The witness's `D` at `c_α` with `α.sum = 2` is the invariant of the `4 × 6` rectangle at the
level `9/2`**, in the grading `ℓ = α.length`, at every admissible separating level. The level is
discharged by `HJO.Mellit.sweepWitness_D_compColouring_congr_level`, and the multiplier and the
number of parts are the readings `HJO.Mellit.colourMult_compColouring` and
`HJO.Mellit.colourParts_compColouring` make of the colouring. -/
theorem sweepWitness_D_two_three_two (q u : L) {α : List ℕ} (hpos : ∀ x ∈ α, 0 < x)
    (hsum : α.sum = 2) {η : ℚ} (hηa : IsAdmissibleLevel η) (hηs : SeparatesDiagonal 2 3 2 η) :
    (sweepWitness q u 2 3).D η (compColouring 2 3 α)
      = sweepIn q u 2 3 α.length (dsc q u 2 3 2 (sepLevel 2 2) (compColouring 2 3 α)) := by
  have hηs' : SeparatesDiagonal 2 3 α.sum η := by rw [hsum]; exact hηs
  have hs2 : SeparatesDiagonal 2 3 α.sum (sepLevel 2 2) := by
    rw [hsum]; exact separatesDiagonal_sepLevel' 2 3 2
  rw [sweepWitness_D_compColouring_congr_level q u (by decide) (by omega) (by omega) hpos
      hηa hηs' (isAdmissibleLevel_sepLevel 2 2) hs2]
  change sweepIn q u 2 3 (colourParts (compColouring 2 3 α))
      (dsc q u 2 3 (colourMult 3 (compColouring 2 3 α)) (sepLevel 2 2) (compColouring 2 3 α)) = _
  rw [colourMult_compColouring (by omega), colourParts_compColouring (by omega) (by omega) hpos,
    hsum]

/-! ### The clause at `N = 2` is a statement about `HJO.Mellit.dsc` alone -/

/-- **The clause of `HJO.Mellit.mellitInduction_sweepWitness` at `(a,b) = (2,3)`, `N = 2` is
equivalent to one identity in `HJO.Sweep.Total L`.** Both quantifiers of the clause — over
replication families and over admissible separating levels — are removed, in both directions:

* the family, because `HJO.Mellit.sweepWitness_stageWord_sweepIn` says the stage word at this
  witness does not depend on which family is taken, and `HJO.Mellit.exists_isReplicationFamily`
  exhibits one, so the forward direction is not vacuous;
* the level, because `HJO.Mellit.sweepWitness_D_two_three_two` says the invariant does not depend on
  which admissible separating level is taken, and `HJO.Mellit.sepLevel 2 2 = 9/2` is one.

The passage from the grading to `HJO.Sweep.Total L` is `HJO.Mellit.sweepIn_injective`: the grading
is a direct summand, so an identity between two of its elements is an identity of total vectors.
Nothing is weakened — the left side is the clause's own body, instantiated. -/
theorem mellitInduction_two_three_two_iff (q u : L) {α : List ℕ} (hpos : ∀ x ∈ α, 0 < x)
    (hsum : α.sum = 2) :
    (∀ Ω, IsReplicationFamily (sweepWitness q u 2 3) Ω →
        ∀ η : ℚ, IsAdmissibleLevel η → SeparatesDiagonal 2 3 2 η →
          (sweepWitness q u 2 3).D η (compColouring 2 3 α)
            = ((-1 : L) ^ ((2 - 1) * 2) * (q * u) ^ ((α.length : ℤ) - ((2 : ℕ) : ℤ))) •
                stageWord (sweepWitness q u 2 3) Ω 2 3 α)
      ↔ dsc q u 2 3 2 (sepLevel 2 2) (compColouring 2 3 α)
          = ((-1 : L) ^ ((2 - 1) * 2) * (q * u) ^ ((α.length : ℤ) - ((2 : ℕ) : ℤ))) •
              stageWordTotal q u 2 3 α := by
  constructor
  · intro h
    obtain ⟨Ω, hΩ⟩ := exists_isReplicationFamily (sweepWitness q u 2 3)
    have key := h Ω hΩ (sepLevel 2 2) (isAdmissibleLevel_sepLevel 2 2)
      (separatesDiagonal_sepLevel' 2 3 2)
    rw [sweepWitness_D_two_three_two q u hpos hsum (isAdmissibleLevel_sepLevel 2 2)
        (separatesDiagonal_sepLevel' 2 3 2),
      sweepWitness_stageWord_sweepIn (by decide) (by omega) (by omega) hΩ α, ← map_smul] at key
    exact sweepIn_injective q u 2 3 α.length key
  · intro h Ω hΩ η hηa hηs
    rw [sweepWitness_D_two_three_two q u hpos hsum hηa hηs,
      sweepWitness_stageWord_sweepIn (by decide) (by omega) (by omega) hΩ α, ← map_smul, h]

/-- **The statement the equivalence above is about is the clause's own body, not a weakening of
it.** The whole of the proof is `fun Ω hΩ η hηa hηs => h Ω hΩ 2 η hηa hηs α hpos hsum` — every
argument is one of `HJO.Mellit.MellitInduction`'s own binders, instantiated, with nothing adjusted
on the way. So the left-hand side of `HJO.Mellit.mellitInduction_two_three_two_iff` is that clause
read at `N = 2` and `(a,b) = (2,3)`, up to no reformulation at all; a statement that had drifted
from the clause could not close this goal by instantiation.

This is the check that decides whether the equivalence is worth anything: the value of reducing an
instance depends entirely on the instance being the clause's, and a hand-transcribed `Prop` that
merely looks like it is worth nothing. -/
theorem mellitInduction_two_three_two_apply_of_clause
    (h : MellitInduction (sweepWitness q u 2 3) 2 3) {α : List ℕ} (hpos : ∀ x ∈ α, 0 < x)
    (hsum : α.sum = 2) :
    ∀ Ω, IsReplicationFamily (sweepWitness q u 2 3) Ω →
      ∀ η : ℚ, IsAdmissibleLevel η → SeparatesDiagonal 2 3 2 η →
        (sweepWitness q u 2 3).D η (compColouring 2 3 α)
          = ((-1 : L) ^ ((2 - 1) * 2) * (q * u) ^ ((α.length : ℤ) - ((2 : ℕ) : ℤ))) •
              stageWord (sweepWitness q u 2 3) Ω 2 3 α :=
  fun Ω hΩ η hηa hηs => h Ω hΩ 2 η hηa hηs α hpos hsum

/-! ### `α = (1,1)`: the clause is one polynomial identity, with the scalar gone -/

/-- **The clause at `(a,b) = (2,3)`, `N = 2`, `α = (1,1)` is equivalent to
`D_{9/2,c_{(1,1)}} = q·e_1^2y_1^2y_2^2 + q(q-1)·e_2y_1^2y_2^2 − qu·e_1(y_1^3y_2^2 + y_1^2y_2^3)
+ qu^2·y_1^3y_2^3`.**

At `ℓ = N = 2` the clause's scalar `(-1)^{(a-1)N}(qu)^{ℓ-N}` is `(-1)^2(qu)^0 = 1`, so the identity
carries no scalar at all, and the right-hand side is the closed form
`HJO.Sweep.stageWordTotal_two_three_one_one`. What is left is a statement about the sweep side
alone: the invariant of the `4 × 6` rectangle at the colouring `c_{(1,1)}`, which by
`HJO.Mellit.card_aboveDiagonal_compColouring_two_three_one_one` is carried by four above-diagonal
paths. Evaluating it is not done here; see the module docstring for where it stands. -/
theorem mellitInduction_two_three_one_one_iff_dsc (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    (∀ Ω, IsReplicationFamily (sweepWitness q u 2 3) Ω →
        ∀ η : ℚ, IsAdmissibleLevel η → SeparatesDiagonal 2 3 2 η →
          (sweepWitness q u 2 3).D η (compColouring 2 3 [1, 1])
            = ((-1 : L) ^ ((2 - 1) * 2)
                * (q * u) ^ ((([1, 1] : List ℕ).length : ℤ) - ((2 : ℕ) : ℤ))) •
                stageWord (sweepWitness q u 2 3) Ω 2 3 [1, 1])
      ↔ dsc q u 2 3 2 (sepLevel 2 2) (compColouring 2 3 [1, 1])
          = q • (MvPolynomial.C (elemSymm L 1 * elemSymm L 1)
                * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2))
            + (q * (q - 1)) • (MvPolynomial.C (elemSymm L 2)
                * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2))
            - (q * u) • (MvPolynomial.C (elemSymm L 1)
                * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2))
            - (q * u) • (MvPolynomial.C (elemSymm L 1)
                * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3))
            + (q * u ^ 2) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3) := by
  rw [mellitInduction_two_three_two_iff q u (by simp) rfl,
    stageWordTotal_two_three_one_one hq0 hu0 hq1]
  norm_num

/-- **What the clause *gives* at `α = (1,1)`: the invariant of the `4 × 6` rectangle, in closed
form.** The equivalence composed with the instantiation check
`HJO.Mellit.mellitInduction_two_three_two_apply_of_clause`, so the hypothesis is
`HJO.Mellit.MellitInduction` itself and nothing else. Reading it the other way: to decide the clause
at this instance it is necessary and sufficient to evaluate
`HJO.Mellit.dsc q u 2 3 2 (HJO.Mellit.sepLevel 2 2) (HJO.Mellit.compColouring 2 3 [1,1])`. -/
theorem dsc_two_three_one_one_of_clause (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (h : MellitInduction (sweepWitness q u 2 3) 2 3) :
    dsc q u 2 3 2 (sepLevel 2 2) (compColouring 2 3 [1, 1])
      = q • (MvPolynomial.C (elemSymm L 1 * elemSymm L 1)
            * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2))
        + (q * (q - 1)) • (MvPolynomial.C (elemSymm L 2)
            * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2))
        - (q * u) • (MvPolynomial.C (elemSymm L 1)
            * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2))
        - (q * u) • (MvPolynomial.C (elemSymm L 1)
            * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3))
        + (q * u ^ 2) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3) :=
  (mellitInduction_two_three_one_one_iff_dsc hq0 hu0 hq1).1
    (mellitInduction_two_three_two_apply_of_clause h (by simp) rfl)

/-! ### `α = (2)`: the first `ℓ < N` instance, reduced to the decided `N = 1` one -/

/-- **The clause at `(a,b) = (2,3)`, `N = 2`, `α = (2)` — the first instance with `ℓ < N` — is
equivalent to `D_{9/2,c_{(2)}} = -(qu)^{-1}Z^{(1)}_{2,3}(D_{5/2,c_{(1)}})`.**

Every trace of the stage word is gone from the right-hand side. What replaces it is one application
of the replicated letter `Z^{(1)}_{2,3}` of `HJO.Mellit.replicatedLetter` to the invariant of the
`2 × 3` rectangle, which `HJO.Mellit.dsc_two_three_one` evaluates and
`HJO.Mellit.mellitInduction_two_three_one_apply` has already decided the clause at. So the first
`ℓ < N` instance is a statement about `HJO.Mellit.dsc` at two rectangles and one explicit operator,
with no stage word and no replication family in it.

The inverse power is where the two sides meet and it does not degenerate: the clause's factor
`(qu)^{ℓ-N} = (qu)^{-1}` is genuine here, and it is exactly the inverse that `Z^{(1)}_{2,3}`
carries through `HJO.Sweep.slopeOperator`'s `(qu)^{-1}z_1`. That is what `q ≠ 0` and `u ≠ 0` are
spent on; `q ≠ 1` is the `q^2/(1-q)` of `HJO.Sweep.zop` inside the same letter. -/
theorem mellitInduction_two_three_two_iff_dsc (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    (∀ Ω, IsReplicationFamily (sweepWitness q u 2 3) Ω →
        ∀ η : ℚ, IsAdmissibleLevel η → SeparatesDiagonal 2 3 2 η →
          (sweepWitness q u 2 3).D η (compColouring 2 3 [2])
            = ((-1 : L) ^ ((2 - 1) * 2)
                * (q * u) ^ ((([2] : List ℕ).length : ℤ) - ((2 : ℕ) : ℤ))) •
                stageWord (sweepWitness q u 2 3) Ω 2 3 [2])
      ↔ dsc q u 2 3 2 (sepLevel 2 2) (compColouring 2 3 [2])
          = (q * u)⁻¹ • replicatedTotal q u 2 3 0
              (-(dsc q u 2 3 1 (sepLevel 2 1) (compColouring 2 3 [1]))) := by
  rw [mellitInduction_two_three_two_iff q u (by simp) rfl,
    stageWordTotal_two_three_two_eq_replicated_neg_dsc hq0 hu0 hq1]
  norm_num

/-- **What the clause *gives* at `α = (2)`: the sweep side satisfies the replication recursion.**
The equivalence composed with the instantiation check
`HJO.Mellit.mellitInduction_two_three_two_apply_of_clause`. Together with
`HJO.Mellit.mellitInduction_two_three_one_apply`, which has already decided the clause at `N = 1`,
this says exactly what the first `ℓ < N` instance adds over the decided one: that lowering `N = 1`'s
invariant by one replicated letter and dividing by `qu` reaches `N = 2`'s. Nothing about the stage
word survives on either side. -/
theorem dsc_two_three_two_of_clause (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (h : MellitInduction (sweepWitness q u 2 3) 2 3) :
    dsc q u 2 3 2 (sepLevel 2 2) (compColouring 2 3 [2])
      = (q * u)⁻¹ • replicatedTotal q u 2 3 0
          (-(dsc q u 2 3 1 (sepLevel 2 1) (compColouring 2 3 [1]))) :=
  (mellitInduction_two_three_two_iff_dsc hq0 hu0 hq1).1
    (mellitInduction_two_three_two_apply_of_clause h (by simp) rfl)

/-! ### Neither instance is vacuous -/

/-- **Neither quantifier of the two instances is vacuous.** The replication family
`HJO.Mellit.exists_isReplicationFamily` produces, and the level `HJO.Mellit.sepLevel 2 2 = 9/2`,
which `HJO.Mellit.isAdmissibleLevel_sepLevel` and `HJO.Mellit.separatesDiagonal_sepLevel'` show is
admissible and separating for `N = 2`, are exhibited together with the clause's own body at both
compositions of `2`.

This check is worth making: every statement of the Mellit layer opens "let
`Ω` be a replication family", so with no instance exhibited each of them is vacuously true,
and the same trap sits on the level — a clause quantified over
admissible separating levels says nothing if there are none. Here both are inhabited at `N = 2`, so
the equivalences above are about identities that are actually asserted. -/
theorem mellitInduction_two_three_two_nonvacuous (q u : L) {α : List ℕ}
    (hpos : ∀ x ∈ α, 0 < x) (hsum : α.sum = 2)
    (h : MellitInduction (sweepWitness q u 2 3) 2 3) :
    ∃ Ω, IsReplicationFamily (sweepWitness q u 2 3) Ω ∧
      IsAdmissibleLevel (sepLevel 2 2) ∧ SeparatesDiagonal 2 3 2 (sepLevel 2 2) ∧
        (sweepWitness q u 2 3).D (sepLevel 2 2) (compColouring 2 3 α)
          = ((-1 : L) ^ ((2 - 1) * 2) * (q * u) ^ ((α.length : ℤ) - ((2 : ℕ) : ℤ))) •
              stageWord (sweepWitness q u 2 3) Ω 2 3 α := by
  obtain ⟨Ω, hΩ⟩ := exists_isReplicationFamily (sweepWitness q u 2 3)
  exact ⟨Ω, hΩ, isAdmissibleLevel_sepLevel 2 2, separatesDiagonal_sepLevel' 2 3 2,
    mellitInduction_two_three_two_apply_of_clause h hpos hsum Ω hΩ (sepLevel 2 2)
      (isAdmissibleLevel_sepLevel 2 2) (separatesDiagonal_sepLevel' 2 3 2)⟩

/-! ### What the left-hand side at `α = (1,1)` is a sum of -/

/-- The above-diagonal `(4,6)`-path `(0,2,3,5,6)`. -/
def baseTwoThreeTwoA : Paths.Heights 2 3 2 := ![0, 2, 3, 5, 6]

/-- The above-diagonal `(4,6)`-path `(0,2,3,6,6)`. -/
def baseTwoThreeTwoB : Paths.Heights 2 3 2 := ![0, 2, 3, 6, 6]

/-- The above-diagonal `(4,6)`-path `(0,3,3,5,6)`. -/
def baseTwoThreeTwoC : Paths.Heights 2 3 2 := ![0, 3, 3, 5, 6]

/-- The above-diagonal `(4,6)`-path `(0,3,3,6,6)`. -/
def baseTwoThreeTwoD : Paths.Heights 2 3 2 := ![0, 3, 3, 6, 6]

set_option maxRecDepth 4000000 in
/-- **The four paths of the `α = (1,1)` instance, named.** The above-diagonal paths of the `4 × 6`
rectangle whose colouring at the level `9/2` is `c_{(1,1)}` are exactly these four: each is
above-diagonal and coloured `c_{(1,1)}` — one `decide` apiece — and the count
`HJO.Mellit.card_aboveDiagonal_compColouring_two_three_one_one` says there are no others. The four
are the two choices of `ŷ_1 ∈ {2,3}` times the two choices of `ŷ_3 ∈ {5,6}`, all with `ŷ_2 = 3`,
which is the diagonal touch point the two-part composition asks for.

These are the four sweep words the left-hand side of this instance is the sum of; each is a product
of eight to ten event operators of `HJO.Mellit.sweepOperator`, read at widths reaching `4`. -/
theorem filter_aboveDiagonal_compColouring_two_three_one_one :
    ({y : Paths.Heights 2 3 2 | Paths.IsAboveDiagonal y ∧
        colouring y (sepLevel 2 2) = compColouring 2 3 [1, 1]} : Finset (Paths.Heights 2 3 2))
      = {baseTwoThreeTwoA, baseTwoThreeTwoB, baseTwoThreeTwoC, baseTwoThreeTwoD} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rw [Finset.mem_filter]
    rcases hy with rfl | rfl | rfl | rfl <;>
        exact ⟨Finset.mem_univ _, by decide +kernel, by decide +kernel⟩
  · rw [card_aboveDiagonal_compColouring_two_three_one_one]
    decide +kernel

/-! ### How many traces each instance's sum has -/

set_option maxRecDepth 4000000 in
/-- **The sum of `HJO.Mellit.dsc` at `c_{(1,1)}` has four terms.** The index set of
`HJO.Mellit.dsc` is `HJO.Mellit.traceIndex`, the *image* of the paths coloured `c_{(1,1)}` under
`τ_{9/2}(·)`, so a priori it could be smaller than the number of those paths; it is not. Four paths,
four distinct traces. -/
theorem card_traceIndex_two_three_one_one :
    #(traceIndex 2 3 2 (sepLevel 2 2) (compColouring 2 3 [1, 1])) = 4 := by
  decide +kernel

set_option maxRecDepth 4000000 in
/-- **The sum of `HJO.Mellit.dsc` at `c_{(2)}` has nineteen terms.** The measurement
`HJO.Mellit.card_aboveDiagonal_compColouring_two_three_two` counts the *paths* coloured `c_{(2)}` at
the level `9/2` and gets nineteen; this counts the traces those paths realize, which is what
`HJO.Mellit.dsc` actually sums over, and finds no collapse. So the left-hand side of the first
`ℓ < N` instance is a sum of nineteen sweep words, not fewer — which is why
`HJO.Mellit.mellitInduction_two_three_two_iff_dsc` routes around it rather than through it. -/
theorem card_traceIndex_two_three_two :
    #(traceIndex 2 3 2 (sepLevel 2 2) (compColouring 2 3 [2])) = 19 := by
  decide +kernel

/-! ### Both instances are in range -/

omit [Algebra ℚ L] in
/-- **Both instances are strictly inside `HJO.Mellit.MellitInput`'s quantification, checked.** The
three range conditions on the slope pair are discharged by `decide` and the three parameter
hypotheses of the equivalences above are *derived* from the one hypothesis `MellitInput` carries on
the field — `HJO.Standing.q_ne_zero`, `HJO.Standing.u_ne_zero`, `HJO.Standing.one_sub_q_ne_zero`.
So nothing is assumed of `q` and `u` beyond `AlgebraicIndependent ℤ ![q, u]`.

This rules out a decision at a degenerate instance: a verdict at
`a = 1`, `q = 1` or `u = 0` settles nothing, because each lies outside the quantification, and at
`q = 1` or `u = 0` a letter carrying `(qu)^{-1}` or `q^2/(1-q)` degenerates to the zero map and
turns the clause false rather than vacuous. None of them is reachable from this hypothesis. -/
theorem two_three_two_in_range (hqu : AlgebraicIndependent ℤ ![q, u]) :
    Nat.Coprime 2 3 ∧ 1 < 2 ∧ (2 : ℕ) < 3 ∧ q ≠ 0 ∧ u ≠ 0 ∧ q ≠ 1 :=
  ⟨by decide, by decide, by decide, Standing.q_ne_zero hqu, Standing.u_ne_zero hqu,
    fun h => Standing.one_sub_q_ne_zero hqu (by rw [h, sub_self])⟩

end HJO.Mellit

end
