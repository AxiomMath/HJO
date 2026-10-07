/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepAppendTwoThree
public import HJO.Shuffle.MellitTwoPartTwoThree
public import HJO.Shuffle.SweepWitnessLhsSingleton
public import HJO.Shuffle.SweepWitnessBraid
public import HJO.Shuffle.MellitLevelRaise
public import HJO.Macdonald.StandingFacts

/-! # `HJO.Mellit.MellitInduction` at the sweep witness, decided at `(a,b) = (2,3)`, `α = (1)`

`HJO.Mellit.MellitInduction` (`HJO/Shuffle/Mellit.lean`) asserts
`D_{η,c_α} = (-1)^{(a-1)N}(qu)^{ℓ-N} G_{ℓ,α_ℓ} ⋯ G_{1,α_1}(1)`
for every replication family, every admissible separating level and every composition of `N` with
positive parts. It is the one clause of `HJO.Mellit.MellitInput` carried as a hypothesis, and the
question this file answers is not whether it can be *proved* but whether it is *true* at
`HJO.Mellit.sweepWitness` — because a false clause needs a new witness, not a new proof route.

## The verdict

It is TRUE at `(a,b) = (2,3)`, `N = 1`, `α = (1)`, at every admissible separating level, for every
`q ∉ {0,1}` and every `u ≠ 0` — `HJO.Mellit.mellitInduction_two_three_one_apply`. The instance is
strictly inside the quantification of `HJO.Mellit.MellitInput`: `a = 2 > 1`, `a < b = 3`,
`Nat.Coprime 2 3`, and the parameter hypotheses are implied by `AlgebraicIndependent ℤ ![q, u]`.
No letter of the witness degenerates there: the clause's own `(qu)^{ℓ-N}` is `(qu)^0 = 1`, and the
two inverses the right-hand side carries — `(qu)^{-1}` from `HJO.Sweep.slopeOperator` and
`(1-q)^{-1}` from `HJO.Sweep.zop` — are exactly what `q ∉ {0,1}` and `u ≠ 0` keep alive.

## Both sides, evaluated

Both sides land in the grading `ℓ = 1` of `HJO.Mellit.Graded`, and the grading is a direct summand
(`HJO.Mellit.sweepIn_injective`), so the clause at this instance is an identity in
`HJO.Sweep.Total L`. The two sides are already computed elsewhere, by wholly independent
routes, and they agree:

* **Left.** `HJO.Mellit.dsc_two_three_one` sums the two words of the `2 × 3` rectangle —
  `HJO.Mellit.aboveReturnPaths_two_three_one` is `{(0,2,3), (0,3,3)}` — and gets
  `D_{5/2,c_{(1)}} = e_1y_1^2 - uy_1^3`. The witness's `D` reads `N` and `ℓ` back off the colouring
  (`HJO.Mellit.colourMult_compColouring`, `HJO.Mellit.colourParts_compColouring`), and
  `HJO.Mellit.sweepWitness_D_compColouring_congr_level` removes the choice of level.
* **Right.** `HJO.Mellit.sweepWitness_stageWord_sweepIn` discharges the replication family: at this
  witness every family gives the same value, `HJO.Mellit.stageWordTotal`. At `α = (1)` that is one
  stage (`HJO.Mellit.stageWordTotal_singleton`), which
  `HJO.Sweep.stageTotal_two_three_zero_one_one` evaluates to `-e_1y_1^2 + uy_1^3`.

The clause's scalar is `(-1)^{(a-1)N}(qu)^{ℓ-N} = (-1)^1(qu)^0 = -1`, and `-1` times the right-hand
value is the left-hand value on the nose. The `u`-terms matching is the load-bearing part: on the
left the `u` comes from the one type-`E` event of the path `(0,3,3)`, and on the right from the
wrap-around letter of `HJO.Sweep.cycleShift` inside `d^*_+`.

## What this does not settle

Only `ℓ = N`. The first instance with `ℓ < N` — where `(qu)^{ℓ-N}` is a genuine inverse power — is
`(a,b) = (2,3)`, `N = 2`, `α = (2)`, and it is out of reach of the method used here:
`HJO.Mellit.card_aboveDiagonal_compColouring_two_three_two` measures it, and `c_{(2)}` is the
colouring of **nineteen** distinct above-diagonal paths of the `4 × 6` rectangle at
`HJO.Mellit.sepLevel 2 2 = 9/2`. So `HJO.Mellit.dsc` there is a sum over the traces of nineteen
paths, against the two of `HJO.Mellit.dsc_two_three_one`. Nothing in this file bears on it either
way, and in particular nothing here is evidence that the clause holds at `ℓ < N`.

The cheap instance at `N = 2` is the *other* one, which is not what the shape of the clause
suggests: `HJO.Mellit.card_aboveDiagonal_compColouring_two_three_one_one` shows `c_{(1,1)}` is
carried by only four paths. That one still has `ℓ = N`, so it does not test the inverse power, but
it is the next instance this method can reach.
-/

@[expose] public section

namespace HJO.Mellit

open Finset HJO.Sym HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The left-hand side: the witness's `D` at `c_{(1)}` -/

/-- **The witness's `D` at `c_{(1)}` in the `2 × 3` rectangle is `e_1y_1^2 - uy_1^3`**, in the
grading `1`, at every admissible separating level.

Three things are discharged here and none of them is bookkeeping. The level is discharged by
`HJO.Mellit.sweepWitness_D_compColouring_congr_level`, so the clause's `∀ η` costs nothing. The
multiplier and the number of parts are read back off the colouring by the witness's `D` field, and
`HJO.Mellit.colourMult_compColouring` and `HJO.Mellit.colourParts_compColouring` say those readings
are `N = 1` and `ℓ = 1`. The value itself is `HJO.Mellit.dsc_two_three_one`. -/
theorem sweepWitness_D_two_three_one (q u : L) (hq0 : q ≠ 0) (hq1 : q ≠ 1) {η : ℚ}
    (hηa : IsAdmissibleLevel η) (hηs : SeparatesDiagonal 2 3 1 η) :
    (sweepWitness q u 2 3).D η (compColouring 2 3 [1])
      = sweepIn q u 2 3 1 (MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 : Total L) ^ 2
          - scal u * (MvPolynomial.X 0 : Total L) ^ 3) := by
  have hpos : ∀ x ∈ ([1] : List ℕ), 0 < x := by simp
  rw [sweepWitness_D_compColouring_congr_level q u (by decide) (by omega) (by omega) hpos
      hηa hηs (isAdmissibleLevel_sepLevel 2 1) (separatesDiagonal_sepLevel' 2 3 1)]
  change sweepIn q u 2 3 (colourParts (compColouring 2 3 [1]))
      (dsc q u 2 3 (colourMult 3 (compColouring 2 3 [1])) (sepLevel 2 1)
        (compColouring 2 3 [1])) = _
  rw [colourMult_compColouring (by omega), colourParts_compColouring (by omega) (by omega) hpos,
    show ([1] : List ℕ).sum = 1 from rfl, show ([1] : List ℕ).length = 1 from rfl,
    dsc_two_three_one q u hq0 hq1]

/-! ### The right-hand side: the stage word at `α = (1)` -/

/-- **The stage word at `(a,b) = (2,3)`, `α = (1)` is `-e_1y_1^2 + uy_1^3`**, in the grading `1`,
for every replication family.

The family is discharged by `HJO.Mellit.sweepWitness_stageWord_sweepIn`, which is the statement that
at this witness the value does not depend on which family is taken — so the clause's `∀ Ω` costs
nothing either. `HJO.Mellit.stageWordTotal_singleton` cuts the one-part word down to one stage and
`HJO.Sweep.stageTotal_two_three_zero_one_one` evaluates it. -/
theorem sweepWitness_stageWord_two_three_one (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    {Ω : ℕ → ℕ → ℕ → ((sweepWitness q u 2 3).W →ₗ[L] (sweepWitness q u 2 3).W)}
    (hΩ : IsReplicationFamily (sweepWitness q u 2 3) Ω) :
    stageWord (sweepWitness q u 2 3) Ω 2 3 [1]
      = sweepIn q u 2 3 1 (-(MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 : Total L) ^ 2)
          + u • (MvPolynomial.X 0 : Total L) ^ 3) := by
  rw [sweepWitness_stageWord_sweepIn (by decide) (by omega) (by omega) hΩ [1],
    stageWordTotal_singleton, stageTotal_two_three_zero_one_one hq0 hu0 hq1]
  rfl

/-! ### The clause, decided -/

/-- **`HJO.Mellit.MellitInduction` at the sweep witness is TRUE at `(a,b) = (2,3)`, `N = 1`,
`α = (1)`.** Verbatim the body of that clause with `Ω`, `N`, `η` and `α` instantiated, at every
replication family and every admissible separating level, for every `q ∉ {0,1}` and `u ≠ 0`.

Both sides are `e_1y_1^2 - uy_1^3` in the grading `1`: the left by
`HJO.Mellit.sweepWitness_D_two_three_one` and the right by
`HJO.Mellit.sweepWitness_stageWord_two_three_one` after the clause's scalar
`(-1)^{(a-1)N}(qu)^{ℓ-N} = -1` is applied. Nothing is weakened and nothing is assumed of the
substrate: `D` is `HJO.Mellit.dsc` on the actual paths and the stage word is
`HJO.Mellit.stage` in the actual operators.

The three hypotheses are the inverses the two sides carry, and each is implied by
`AlgebraicIndependent ℤ ![q, u]`, which is the hypothesis `HJO.Mellit.MellitInput` is stated at. So
this is a decision at an instance strictly inside the quantification, not at a degenerate corner —
see the module docstring. -/
theorem mellitInduction_two_three_one_apply (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    {Ω : ℕ → ℕ → ℕ → ((sweepWitness q u 2 3).W →ₗ[L] (sweepWitness q u 2 3).W)}
    (hΩ : IsReplicationFamily (sweepWitness q u 2 3) Ω) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal 2 3 1 η) :
    (sweepWitness q u 2 3).D η (compColouring 2 3 [1])
      = ((-1 : L) ^ ((2 - 1) * 1) * (q * u) ^ ((([1] : List ℕ).length : ℤ) - (1 : ℕ))) •
          stageWord (sweepWitness q u 2 3) Ω 2 3 [1] := by
  rw [sweepWitness_D_two_three_one q u hq0 hq1 hηa hηs,
    sweepWitness_stageWord_two_three_one hq0 hu0 hq1 hΩ, ← map_smul]
  congr 1
  rw [scal_mul_eq_smul_total]
  norm_num
  module

/-- **The statement decided above is the clause's own body, not a weakening of it.** The whole of
the proof is `h Ω hΩ 1 η hηa hηs [1] hpos rfl` — every argument is one of
`HJO.Mellit.MellitInduction`'s own binders, instantiated, and nothing is adjusted on the way. So
`HJO.Mellit.mellitInduction_two_three_one_apply` is that clause read at `N = 1`, `α = (1)` and
`(a,b) = (2,3)`, up to no reformulation at all; a statement that had drifted from the clause could
not close this goal by instantiation.

This is the check that matters for the verdict. The value of deciding an instance depends entirely
on the instance being the clause's, and a hand-transcribed `Prop` that merely looks like it is
worth nothing. -/
theorem mellitInduction_two_three_one_apply_of_clause
    (h : MellitInduction (sweepWitness q u 2 3) 2 3)
    {Ω : ℕ → ℕ → ℕ → ((sweepWitness q u 2 3).W →ₗ[L] (sweepWitness q u 2 3).W)}
    (hΩ : IsReplicationFamily (sweepWitness q u 2 3) Ω) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal 2 3 1 η) :
    (sweepWitness q u 2 3).D η (compColouring 2 3 [1])
      = ((-1 : L) ^ ((2 - 1) * 1) * (q * u) ^ ((([1] : List ℕ).length : ℤ) - (1 : ℕ))) •
          stageWord (sweepWitness q u 2 3) Ω 2 3 [1] :=
  h Ω hΩ 1 η hηa hηs [1] (by simp) rfl

/-- **The clause at this instance, in the shape `HJO.Mellit.MellitInduction` states it.** The same
content as `HJO.Mellit.mellitInduction_two_three_one_apply` with the composition quantified and
pinned, which is the form in which the clause's own body is read: every side condition the clause
imposes on `α` — positive parts, sum `N` — is discharged, so no weakening can hide in the shape. -/
theorem mellitInduction_two_three_one (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    ∀ Ω, IsReplicationFamily (sweepWitness q u 2 3) Ω →
      ∀ η : ℚ, IsAdmissibleLevel η → SeparatesDiagonal 2 3 1 η →
        ∀ α : List ℕ, α = [1] → (∀ x ∈ α, 0 < x) → α.sum = 1 →
          (sweepWitness q u 2 3).D η (compColouring 2 3 α)
            = ((-1 : L) ^ ((2 - 1) * 1) * (q * u) ^ ((α.length : ℤ) - (1 : ℕ))) •
                stageWord (sweepWitness q u 2 3) Ω 2 3 α := by
  rintro Ω hΩ η hηa hηs α rfl - -
  exact mellitInduction_two_three_one_apply hq0 hu0 hq1 hΩ hηa hηs

/-- **Neither quantifier of the instance is vacuous.** The same identity with the replication family
and the level *exhibited*: the one `HJO.Mellit.exists_isReplicationFamily`
produces, and `HJO.Mellit.sepLevel 2 1 = 5/2`, which `HJO.Mellit.isAdmissibleLevel_sepLevel` and
`HJO.Mellit.separatesDiagonal_sepLevel'` show is admissible and separating.

This check is worth making: every statement of the Mellit layer opens "let
`Ω` be a replication family", so with no instance exhibited each of them is vacuously true. The same
trap sits on the level — a clause quantified over admissible separating levels says nothing if there
are none. Here both are inhabited, so the verdict above is about an identity that is actually
asserted. -/
theorem mellitInduction_two_three_one_nonvacuous (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    ∃ Ω, IsReplicationFamily (sweepWitness q u 2 3) Ω ∧
      IsAdmissibleLevel (sepLevel 2 1) ∧ SeparatesDiagonal 2 3 1 (sepLevel 2 1) ∧
        (sweepWitness q u 2 3).D (sepLevel 2 1) (compColouring 2 3 [1])
          = ((-1 : L) ^ ((2 - 1) * 1) * (q * u) ^ ((([1] : List ℕ).length : ℤ) - (1 : ℕ))) •
              stageWord (sweepWitness q u 2 3) Ω 2 3 [1] := by
  obtain ⟨Ω, hΩ⟩ := exists_isReplicationFamily (sweepWitness q u 2 3)
  exact ⟨Ω, hΩ, isAdmissibleLevel_sepLevel 2 1, separatesDiagonal_sepLevel' 2 3 1,
    mellitInduction_two_three_one_apply hq0 hu0 hq1 hΩ (isAdmissibleLevel_sepLevel 2 1)
      (separatesDiagonal_sepLevel' 2 3 1)⟩

/-! ### Why the first `ℓ < N` instance is out of reach of this method -/

/-- **`c_{(2)}` is the colouring of nineteen distinct above-diagonal paths of the `4 × 6`
rectangle**, at the separating level `HJO.Mellit.sepLevel 2 2 = 9/2`.

This is the measurement of the next instance, and it is what stops the method used above. The first
instance with `ℓ < N` — where the clause's `(qu)^{ℓ-N}` is a genuine inverse power rather than
`(qu)^0` — is `(a,b) = (2,3)`, `N = 2`, `α = (2)`. `HJO.Mellit.dsc` there is a sum of
`HJO.Mellit.partialSweepWord`s indexed by the *traces* of those paths
(`HJO.Mellit.traceIndex`), so evaluating the left-hand side means evaluating up to nineteen sweep
words in the `4 × 6` rectangle. The two instances evaluated before this one needed one
word (`HJO.Mellit.dsc_one_two_eq`) and two (`HJO.Mellit.dsc_two_three_one`).

For contrast the whole rectangle has only `23` above-diagonal paths, so the colouring condition
rules out just four: `HJO.Mellit.colouring` at `9/2` acquires the extra cells `(1,3)` and `(2,3)`
exactly when `ŷ_2 = 3`, and `ŷ_2 ≥ 4` is the rest. The instance is therefore not a small one, and
nothing in this file bears on whether the clause holds there.

**The instance is nevertheless decided, by another method.** The clause at `α = (2)` is
`HJO.Mellit.mellitInduction_two_three_alphaTwo`
(`HJO/Shuffle/SweepInductionInstanceTwoAlphaDecided.lean`), with all nineteen words
evaluated, and this very cardinality is what its index set was derived from rather than decided (the
`Finset` equality over `Heights 2 3 2` does not reduce under `decide +kernel` in module mode). The
count above is what that evaluation rests on; what is out of reach is only the method of this
file. -/
theorem card_aboveDiagonal_compColouring_two_three_two :
    #{y : Paths.Heights 2 3 2 | Paths.IsAboveDiagonal y ∧
        colouring y (sepLevel 2 2) = compColouring 2 3 [2]} = 19 := by
  set_option maxRecDepth 1000000 in decide +kernel

/-- **The `4 × 6` rectangle has only twenty-three above-diagonal paths in all**, so the colouring
condition of `HJO.Mellit.card_aboveDiagonal_compColouring_two_three_two` excludes only four of
them. -/
theorem card_aboveDiagonal_two_three_two :
    #{y : Paths.Heights 2 3 2 | Paths.IsAboveDiagonal y} = 23 := by
  set_option maxRecDepth 1000000 in decide +kernel

/-- **`c_{(1,1)}` is the colouring of only FOUR above-diagonal paths of the `4 × 6` rectangle**, at
the same level `9/2` — the four that `HJO.Mellit.card_aboveDiagonal_compColouring_two_three_two`
leaves out, since `HJO.Mellit.colouring` at `9/2` picks up the two extra cells `(1,3)` and `(2,3)`
exactly when `ŷ_2 = 3`, and `c_{(1,1)} = {(0,0),(1,3),(2,3),(3,6)}` is `c_{(2)}` plus those two.

So at `N = 2` the *two-part* composition is the cheap instance and the one-part composition is the
expensive one, which is the opposite of what the shape of the clause suggests. `α = (1,1)` has
`ℓ = 2 = N`, so it does not test the inverse power either — but at four words it is within reach of
the method that settled `α = (1)`, and it is the next instance to try. `α = (2)`, the first with
`ℓ < N`, is not. -/
theorem card_aboveDiagonal_compColouring_two_three_one_one :
    #{y : Paths.Heights 2 3 2 | Paths.IsAboveDiagonal y ∧
        colouring y (sepLevel 2 2) = compColouring 2 3 [1, 1]} = 4 := by
  set_option maxRecDepth 1000000 in decide +kernel

/-! ### The instance is in range -/

/-- **The instance is strictly inside `HJO.Mellit.MellitInput`'s quantification, checked.** The
three range conditions `MellitInput` imposes on the slope pair are conjoined to the verdict and
discharged by `decide`, and the three parameter hypotheses are *derived* from the one hypothesis
`MellitInput` carries on the field — `HJO.Standing.q_ne_zero`, `HJO.Standing.u_ne_zero` and
`HJO.Standing.one_sub_q_ne_zero`. So nothing is assumed of `q` and `u` beyond
`AlgebraicIndependent ℤ ![q, u]`, and `a = 2`, `b = 3` satisfy `Nat.Coprime a b`, `1 < a`, `a < b`.

This is what rules out a decision at a degenerate instance: a
verdict at `a = 1`, `q = 1` or `u = 1` settles nothing, because each of those lies outside the
quantification, and at `q = 1` or `u = 0` a letter carrying `(qu)^{-1}` or `q^k/(1-q)` degenerates
to the zero map and turns the clause false rather than vacuous. None of them is reachable from this
hypothesis. -/
theorem mellitInduction_two_three_one_in_range (hqu : AlgebraicIndependent ℤ ![q, u]) :
    Nat.Coprime 2 3 ∧ 1 < 2 ∧ (2 : ℕ) < 3 ∧
      ∀ Ω, IsReplicationFamily (sweepWitness q u 2 3) Ω →
        ∀ η : ℚ, IsAdmissibleLevel η → SeparatesDiagonal 2 3 1 η →
          ∀ α : List ℕ, α = [1] → (∀ x ∈ α, 0 < x) → α.sum = 1 →
            (sweepWitness q u 2 3).D η (compColouring 2 3 α)
              = ((-1 : L) ^ ((2 - 1) * 1) * (q * u) ^ ((α.length : ℤ) - (1 : ℕ))) •
                  stageWord (sweepWitness q u 2 3) Ω 2 3 α :=
  ⟨by decide, by decide, by decide,
    mellitInduction_two_three_one (Standing.q_ne_zero hqu) (Standing.u_ne_zero hqu)
      (fun h => Standing.one_sub_q_ne_zero hqu (by rw [h, sub_self]))⟩

end HJO.Mellit
