/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.GesselReversal
public import HJO.Shuffle.Mellit
public import HJO.Shuffle.SweepWitnessLhs
public meta import HJO.Attr

/-! # `MellitInput` at the sweep witness, and the three statements that remain

`HJO.Mellit.MellitInput` asks for a `HJO.Mellit.SweepSystem` satisfying four clauses. The system is
not in question: `HJO.Mellit.sweepWitness` is a term of that structure, built from the
concrete operators of `HJO.Sweep`. So the existential is discharged, and what the four clauses
cost at that one witness is what this file computes.

Two of the four are already theorems there, and one is reduced:

* `HJO.Mellit.RhsSumsAgree` — a theorem, `HJO.Mellit.rhsSumsAgree_sweepWitness`. Free from the
  construction, the witness's `χ` being `HJO.Paths.sweepChar` by definition.
* `HJO.Mellit.Rem41` — reduced to `HJO.Mellit.SweepComputes` by
  `HJO.Mellit.rem41_of_sweepComputes`, whose two pinning hypotheses the witness satisfies:
  `hchi` by `rfl` and `hD` by `HJO.Mellit.sweepWitness_proj_dminus_pow_D`.
* `HJO.Mellit.LhsRewrite` — equivalent at the witness to `HJO.Mellit.LhsComputes`, by
  `HJO.Mellit.lhsRewrite_sweepWitness_iff_lhsComputes`. An equivalence and not a one-way
  reduction, so nothing is weakened.
* `HJO.Mellit.MellitInduction` — carried as given. It is the one clause with no reduction to a
  statement about the concrete operators; see the implementation note.

`HJO.Mellit.mellitInput_of_three` assembles those into `MellitInput` from three hypotheses, and
`HJO.Mellit.shuffle_of_three` composes it with `HJO.Mellit.shuffle_of_mellit` to reach
`HJO.External.Shuffle`. The point of stating them is that the shuffle side then
has a residual of exactly three named `Prop`s, each about the concrete substrate and each provable
independently: the moment all three are theorems, `HJO.External.Shuffle` is a theorem with no
hypothesis, by `HJO.Mellit.shuffle_of_three` and nothing further.

## Main results

* `HJO.Mellit.mellitInput_of_three`: `LhsComputes`, `MellitInduction` at the witness and
  `SweepComputes`, generically in the parameters, give `MellitInput`.
* `HJO.Mellit.shuffle_of_three`: the same three, with `HJO.GesselReverseSum` (a theorem,
  `HJO.gesselReverseSum`), give `HJO.External.Shuffle`.

## Implementation notes

**Why the hypotheses are stated generically rather than at a fixed `q`, `u`, `a`, `b`.**
`MellitInput` quantifies over the parameters inside itself, so a hypothesis supplied at one
parameter tuple cannot serve it. Each of the three is therefore asked for under exactly the
constraints `MellitInput` itself provides — `AlgebraicIndependent ℤ ![q, u]`, `Nat.Coprime a b`,
`1 < a`, `a < b` — and no others. This matters because the genericity is load-bearing and not
decoration: `HJO.Mellit.not_mellitInput_unrestricted` refutes three of the four clauses jointly at
`q = 0`, `u = 1`, `(a, b) = (2, 3)`, so a version of any of these statements asserted at all `q`,
`u` would be false rather than merely unproved.

**`q ≠ 0` and `0 < a`, `0 < b` are derived, not assumed.** `rhsSumsAgree_sweepWitness` wants
`q ≠ 0`, which follows from `AlgebraicIndependent ℤ ![q, u]` by `HJO.PhiPoly.eq_of_aeval_eq` — the
same route `HJO.Mellit.shuffleAbove_of_mellit` already takes for `u ≠ 0`. The positivity of `a` and
`b` follows from `1 < a` and `a < b` by `omega`. So the three hypotheses carry nothing the clause
did not already give them.

**`MellitInduction` is passed through.** The other three clauses
are stated here as `Prop`s about the concrete operators (`LhsComputes`, `SweepComputes`) or proved
outright (`RhsSumsAgree`); `MellitInduction` is asked for at the witness as itself. It HAS an
equivalent at the witness, `HJO.Mellit.SweepAppend` (via
`HJO.Mellit.mellitInduction_sweepWitness_iff_sweepAppend`), and that equivalent is NOT the route to
it: the obstruction there is a grading mismatch, not a missing lemma — the single `d*₊` inside
`replOneTotal` raises the index by exactly one however large the composition is, while the width
shift `δ` runs over a band and varies with the tail. `HJO/Shuffle/SweepAppendWidth.lean`
carries the counter-witnesses. The route that works is the braid-monoid one,
`HJO.Mellit.braidValueColouring_eq_dsc_floor` then
`HJO.Mellit.invFin_eq_invIni_of_separatesDiagonal`. So the clause is stated here as itself rather
than as `SweepAppend`.

## References

The clauses of `HJO.Mellit.MellitInput` at `HJO.Mellit.sweepWitness`, in terms of
`HJO.shuffleAbove`, `HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc` and
`HJO.Mellit.sweepComputes`.
-/

@[expose] public section

namespace HJO.Mellit

universe w

variable {L : Type w} [Field L] [Algebra ℚ L]

/-- `AlgebraicIndependent ℤ ![q, u]` forces `q ≠ 0`. The companion of the `u ≠ 0` step inside
`HJO.Mellit.shuffleAbove_of_mellit`, by the same route through `HJO.PhiPoly.eq_of_aeval_eq`. -/
theorem ne_zero_of_algebraicIndependent_fst {K : Type*} [Field K] {q u : K}
    (hqu : AlgebraicIndependent ℤ ![q, u]) : q ≠ 0 := fun h0 => by
  have hz : (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ) = 0 :=
    PhiPoly.eq_of_aeval_eq hqu (by simp [h0])
  have hz' := congrArg (MvPolynomial.aeval ![(1 : ℤ), 1]) hz
  simp at hz'

/-- **`MellitInput` from the three statements that remain.** The existential is discharged by
`HJO.Mellit.sweepWitness`; `RhsSumsAgree` is a theorem there; `Rem41` and `LhsRewrite` are
supplied by `HJO.Mellit.SweepComputes` and `HJO.Mellit.LhsComputes`; and `MellitInduction` is
carried.

Each hypothesis is asked for under exactly the constraints `MellitInput` itself provides, since the
genericity is load-bearing: `HJO.Mellit.not_mellitInput_unrestricted` refutes three of the four
clauses jointly at `q = 0`, `u = 1`, `(a, b) = (2, 3)`. -/
theorem mellitInput_of_three
    (hlhs : ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ a b : ℕ, Nat.Coprime a b → 1 < a →
      a < b → LhsComputes q u a b)
    (hind : ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ a b : ℕ, Nat.Coprime a b → 1 < a →
      a < b → MellitInduction (sweepWitness q u a b) a b)
    (hsc : ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ a b : ℕ, Nat.Coprime a b → 1 < a →
      a < b → SweepComputes q u a b) :
    MellitInput L := by
  intro q u hqu a b hab ha hb
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by omega
  refine ⟨sweepWitness q u a b,
    (lhsRewrite_sweepWitness_iff_lhsComputes hab ha0 hb0).2 (hlhs q u hqu a b hab ha hb),
    hind q u hqu a b hab ha hb,
    rem41_of_sweepComputes _ hab ha0 hb0 (fun _ _ _ _ => rfl)
      (fun N η α hpos hsum => sweepWitness_proj_dminus_pow_D q u ha0 hb0 N η hpos hsum)
      (hsc q u hqu a b hab ha hb),
    rhsSumsAgree_sweepWitness ha0 (ne_zero_of_algebraicIndependent_fst hqu)⟩

/-- **`HJO.External.Shuffle` from the three statements that remain.** The whole shuffle side,
with `HJO.GesselReverseSum` discharged by `HJO.gesselReverseSum` and the sweep system
discharged by `HJO.Mellit.sweepWitness`.

The residual is exactly `HJO.Mellit.LhsComputes`, `HJO.Mellit.MellitInduction` at the witness, and
`HJO.Mellit.SweepComputes`. When all three are theorems this gives `HJO.External.Shuffle` with no
hypothesis. -/
theorem shuffle_of_three
    (hlhs : ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ a b : ℕ, Nat.Coprime a b → 1 < a →
      a < b → LhsComputes q u a b)
    (hind : ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ a b : ℕ, Nat.Coprime a b → 1 < a →
      a < b → MellitInduction (sweepWitness q u a b) a b)
    (hsc : ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ a b : ℕ, Nat.Coprime a b → 1 < a →
      a < b → SweepComputes q u a b) :
    HJO.External.Shuffle L :=
  shuffle_of_mellit (gesselReverseSum L) (mellitInput_of_three hlhs hind hsc)

end HJO.Mellit
