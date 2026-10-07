/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.LhsOpAssembly
public import HJO.Shuffle.LhsOpBaseValue
public import HJO.Shuffle.ShuffleDownstream

/-! # The compositional rational shuffle theorem, closed

Mellit's rewriting of the left-hand side (`HJO.Mellit.lhsRewrite_sweepWitness`) is proved at the
standing field `𝕜 = ℚ(q,u)` by the operator chain of `HJO/Shuffle/LhsOp*.lean`: the base slope
`(1,1)` (`HJO.Mellit.LhsDesign.lhsOp_one_one_apply_one`, Carlsson–Mellit's formula for `C_α`, and
`lhsOp_one_one_isMul`), carried to every coprime slope by Mellit's `N` and `S`
(`lhsOp_add_left`, `lhsOp_add_self`, `theta_add_left`, `theta_add_self_nsTransports`). It ascends
to every field with an algebraically independent pair
(`HJO.Mellit.lhsComputes_of_lhsWord_standing`), and with `HJO.Mellit.mellitInduction_sweepWitness`
it gives the shuffle identity outright.

## Main results

* `HJO.Mellit.LhsDesign.lhsWord_standing`: `HJO.Mellit.LhsWord` at `𝕜`, no hypothesis.
* `HJO.Mellit.lhsRewrite_sweepWitness`.
* `HJO.Mellit.lhsComputes_of_algebraicIndependent`: its residual form `HJO.Mellit.LhsComputes`.
* `HJO.shuffleAbove`, the identity above the diagonal, at every field.
* `HJO.Ascent.shuffle`, `HJO.External.Shuffle L` at every field.

With it the two main theorems hold with no hypothesis: `HJO.conjecture` and
`HJO.finiteSeries_eq_qPochhammer_mul_boundedGF`, in `HJO/Main.lean`.
-/

@[expose] public section

namespace HJO.Mellit.LhsDesign

open HJO.Sym HJO.Sweep HJO.Ascent

variable (K : Type*) [Field K] [Algebra ParamRing K] [IsFractionRing ParamRing K] [Algebra ℚ K]

/-- **`HJO.Mellit.lhsRewrite_sweepWitness` at the standing field, in its `Λ`-level form**, with no
hypothesis: `HJO.Mellit.LhsDesign.lhsWord_standing_of_base` with the base value
`HJO.Mellit.LhsDesign.lhsOp_one_one_apply_one`. -/
theorem lhsWord_standing :
    ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b → LhsWord (paramQ K) (paramU K) a b :=
  lhsWord_standing_of_base K fun hnab hone α hpos => lhsOp_one_one_apply_one K hnab hone α hpos

end HJO.Mellit.LhsDesign

namespace HJO.Mellit

open HJO.Ascent

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The residual form of `HJO.Mellit.lhsRewrite_sweepWitness`**: `HJO.Mellit.LhsComputes` at every
pair of algebraically independent parameters and every coprime `1 < a < b`. -/
theorem lhsComputes_of_algebraicIndependent :
    ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b →
      LhsComputes q u a b :=
  lhsComputes_of_lhsWord_standing Kk (LhsDesign.lhsWord_standing Kk)

/-- **Mellit's rewriting of the left-hand side**, at the sweep witness of
`HJO.Sweep.piece`, for every slope homomorphism, every realisation, every replication family and
every composition, at every pair of algebraically independent parameters. This is the clause at the
ambient field `ℚ(q,u)`, generalised to every field of characteristic zero with an
algebraically independent pair; the weaker hypothesis `(1-q)(1-u) ≠ 0` does not suffice
at a general field, since at `qu ∈ {0,1}` every algebra map is a slope map. -/
@[hjo "lem_mellit_lhs_rewrite"]
theorem lhsRewrite_sweepWitness :
    ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b →
      LhsRewrite (sweepWitness q u a b) a b :=
  fun q u hqu a b hab ha hlt =>
    (lhsRewrite_sweepWitness_iff_lhsComputes hab (by omega) (by omega)).2
      (lhsComputes_of_algebraicIndependent q u hqu a b hab ha hlt)

end HJO.Mellit

namespace HJO

/-- **The compositional rational shuffle identity above the diagonal**
(Bergeron–Garsia–Leven–Xin's Conjecture 3.3, proved by Mellit), at every field of characteristic
zero, for every algebraically independent pair of parameters. -/
@[hjo "lem_shuffle_source"]
theorem shuffleAbove (L : Type*) [Field L] [Algebra ℚ L] : ShuffleAbove L :=
  shuffleAbove_of_shuffle (Mellit.shuffle_of_lhs Mellit.lhsComputes_of_algebraicIndependent)

end HJO

namespace HJO.Ascent

/-- **The shuffle input of the challenge file**,
`HJO.External.Shuffle L`, at every field of characteristic zero. -/
@[hjo "prop_challenge_shuffle"]
theorem shuffle (L : Type*) [Field L] [Algebra ℚ L] : External.Shuffle L :=
  Mellit.shuffle_of_lhs Mellit.lhsComputes_of_algebraicIndependent

end HJO.Ascent
