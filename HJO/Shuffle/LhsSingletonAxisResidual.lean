/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.ThetaCompleteHomogAxisTwoThree
public import HJO.Shuffle.SweepReplicatedIterate

/-! # The `hlhs` clause at a one-part composition, with `Θ` eliminated

`HJO.Mellit.lhsAt_two_three_singleton_iff_bop`
(`HJO/Shuffle/SweepReplicatedIterate.lean`) reduces the `hlhs` clause at `[A]` and
`(a,b) = (2,3)` to `Θ(h_A)(1) = -∑_m B_m((G_A)_m)`, which is a decision *procedure* per fixed `A`
and not a decision: the left-hand side still names an arbitrary slope homomorphism.

`HJO/Shuffle/ThetaCompleteHomogAxisTwoThree.lean` computes that left-hand side. This file
substitutes it, and what comes out is the clause with **no `Θ` in it at all**.

## What is proved

* `HJO.Mellit.theta_completeHomog_one_apply_one_eq_sum_bop` — at `A = 1` the two sides agree. The
  creation side is `HJO.Mellit.theta_completeHomog_one_apply_one`, read off `HJO.Sym.axisGen` and
  `HJO.Sym.qop_two_three_apply_one`; the sweep side is
  `HJO.Mellit.sum_bop_stageWordTotal_two_three_one`, the Hall--Littlewood sum of `HJO.Sym.Bop` over
  the monomials of the one-part stage word. The two routes share no lemma, so this is an
  independent consistency check on the axis expansion.

* `HJO.Mellit.lhsAt_two_three_one_of_axis` — consequently the clause at `[1]` **holds**, proved from
  the creation side. The clause at `[1]` was already decided by
  `HJO.Mellit.lhsAt_two_three_one_of_singleton_iff`; what is new is that the axis route reaches the
  same conclusion, which is what licenses using that route at `A ≥ 2`.

* `HJO.Mellit.lhsAt_two_three_two_iff_qop` — the clause at `[2]` is **equivalent to a `Θ`-free
  identity in `Λ`**:

    `-(1 + qu) ∑_m B_m((G_2)_m) = qu (Q_{2,3}(Q_{2,3}1) - Q_{4,6}(1))`.

  Both slope-operator values on the right are computed in closed form over the nine degree-six
  `e`-monomials (`HJO.Sym.qop_two_three_apply_qop_two_three_apply_one`,
  `HJO.Sym.qop_four_six_apply_one`), and
  `HJO.Mellit.theta_completeHomog_two_apply_one` writes their combination out. So the clause at
  `[2]` is now one explicit comparison in `Λ` between a Hall--Littlewood sum and a known
  polynomial.

## What remains at `A = 2`

Exactly one thing: the value of `∑_m B_m((G_2)_m)`, the sweep side at `A = 2`. It is generated from
the seed by one application of `HJO.Mellit.stageWordTotal_singleton_succ`, whose action on `V_1` is
`HJO.Sweep.replicatedTotal_two_three_zero_of_mem_piece`, and it is not computed here. Without it,
this file does not decide the clause at `[2]` — but it is no longer a statement about an arbitrary
homomorphism, and the comparison it asks for is between two polynomials in the same nine monomials.

## Genericity

`q ≠ 0`, `u ≠ 0`, `q ≠ 1`: the hypotheses of `HJO.Mellit.lhsAt_two_three_singleton_iff_bop`,
each the inverse-becomes-zero hazard of `HJO.Sweep.slopeOperator`'s letter `(qu)^{-1}z_1` and
`HJO.Sweep.zop`'s scalar `q/(1-q)`; in a field `0⁻¹ = 0`, so there the clause is false rather than
vacuous.

`M = (1-q)(1-u) ≠ 0`: `HJO.Sym.Qop`'s `M^{-1}`, so also `u ≠ 1`.

`qu ≠ 0`, `qu ≠ 1`: `HJO.Sym.axisGen`'s normalising scalar `v/(v-1)`, without which the axis
generators do not generate and `Θ(h_A)` is not determined. Note `qu ≠ 0` already follows from
`q ≠ 0` and `u ≠ 0`, and is carried separately because that is the shape the axis lemmas take.

`qu ≠ -1` in `HJO.Mellit.lhsAt_two_three_two_iff_qop`: the scalar `1 + qu` must be cancellable for
the equivalence to run in both directions. At `qu = -1` the degree-two axis expansion has zero on
the left and `h_2` is not determined by `U_1, U_2`, so the clause at `[2]` genuinely is not reduced
there.

At algebraically independent `q, u` every one of these holds. A statement at `a = 1`, `q = 1` or
`u = 1` would settle nothing; `(2,3)` is coprime with `1 < a < b`.

## Implementation notes

`HJO.Mellit.lhsAt_two_three_one_of_axis` re-proves an already-decided instance by a second route,
and the other two are reductions of `HJO.Mellit.lhsRewrite_sweepWitness`'s clause rather than the
clause itself.

## References

This file concerns `HJO.Mellit.lhsRewrite_sweepWitness`, using `HJO.Sym.IsSlopeHom`,
`HJO.Sym.axisGen`, `HJO.Sym.Qop`, `HJO.Sym.Bop`, `HJO.Mellit.stage` and `HJO.Sym.completeHomog`.
-/

@[expose] public section

namespace HJO.Mellit

open HJO.Sym HJO.Sweep Finset

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### `A = 1`: the two routes agree -/

/-- **Consistency check.** At `A = 1` the creation side `Θ(h_1)(1)` — computed
from `HJO.Sym.axisGen` by `HJO.Mellit.theta_completeHomog_one_apply_one` — equals minus the
Hall--Littlewood sum of `HJO.Sym.Bop` over the monomials of the one-part stage word, whose value is
`HJO.Mellit.sum_bop_stageWordTotal_two_three_one`.

The two sides are computed by disjoint routes: the left reads the axis prescription and
`HJO.Sym.qop_two_three_apply_one`, the right runs
`HJO.Sweep.dminus_one_stageTotal_two_three_zero_one_one` on the seed. A sign lost in the axis
expansion of `h_A` would separate them here.

Genericity: `M ≠ 0`, `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, `qu ≠ 0`, `qu ≠ 1`. -/
theorem theta_completeHomog_one_apply_one_eq_sum_bop (hM : (1 - q) * (1 - u) ≠ 0) (hq0 : q ≠ 0)
    (hu0 : u ≠ 0) (hq1 : q ≠ 1) (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom 2 3 q u Θ) :
    Θ (completeHomog L 1) 1
      = -∑ d ∈ (stageWordTotal q u 2 3 [1] : Total L).support,
          Bop q ((d 0 : ℕ) : ℤ)
            (MvPolynomial.coeff d (stageWordTotal q u 2 3 [1] : Total L)) := by
  rw [theta_completeHomog_one_apply_one hM hΘ hv0 hv1,
    sum_bop_stageWordTotal_two_three_one hM hq0 hu0 hq1]
  abel

/-- **The clause at `[1]` holds, by the creation side.**
`HJO.Mellit.lhsAt_two_three_singleton_iff_bop` is an equivalence, and
`HJO.Mellit.theta_completeHomog_one_apply_one_eq_sum_bop` discharges its right-hand side.

The instance was already decided by `HJO.Mellit.lhsAt_two_three_one_of_singleton_iff`; the point of
this proof is the *route*. It runs the axis expansion of `HJO.Sym.completeHomog` on
`HJO.Sym.axisGen`, which is the only machinery available at `A ≥ 2`, and arriving at a true
conclusion at `A = 1` is what licenses it there.

Genericity: `M ≠ 0`, `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, `qu ≠ 0`, `qu ≠ 1`. -/
theorem lhsAt_two_three_one_of_axis (hM : (1 - q) * (1 - u) ≠ 0) (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom 2 3 q u Θ) :
    LhsAt q u 2 3 Θ [1] :=
  (lhsAt_two_three_singleton_iff_bop hq0 hu0 hq1 1 Θ).2
    (theta_completeHomog_one_apply_one_eq_sum_bop hM hq0 hu0 hq1 hv0 hv1 hΘ)

/-! ### `A = 2`: the clause with `Θ` eliminated -/

/-- **The clause at `[2]` is a `Θ`-free identity in `Λ`:**

  `-(1 + qu) ∑_m B_m((G_2)_m) = qu (Q_{2,3}(Q_{2,3}1) - Q_{4,6}(1))`.

`HJO.Mellit.lhsAt_two_three_singleton_iff_bop` says the clause is
`Θ(h_2)(1) = -∑_m B_m((G_2)_m)`, and `HJO.Mellit.theta_completeHomog_two_apply_one_smul` computes
`(1 + qu)Θ(h_2)(1)`; multiplying the clause by the cancellable scalar `1 + qu` removes the last
occurrence of `Θ`.

Both operator values on the right are computed in closed form over the nine degree-six `e`-monomials
(`HJO.Sym.qop_two_three_apply_qop_two_three_apply_one`, `HJO.Sym.qop_four_six_apply_one`), and
`HJO.Mellit.theta_completeHomog_two_apply_one` is their combination written out. So what remains
between here and a decision at `A = 2` is the *left*-hand side: the value of the Hall--Littlewood
sum on the one-part stage word at `[2]`, which no declaration supplies.

Genericity: `M ≠ 0`, `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, `qu ≠ 0`, `qu ≠ 1`, and `qu ≠ -1` for the
cancellation — at `qu = -1` the degree-two axis expansion is degenerate and the reduction does not
run. -/
theorem lhsAt_two_three_two_iff_qop (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) (hv0 : q * u ≠ 0)
    (hv1 : q * u ≠ 1) (hvn : q * u + 1 ≠ 0)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom 2 3 q u Θ) :
    LhsAt q u 2 3 Θ [2]
      ↔ -((q * u + 1) • ∑ d ∈ (stageWordTotal q u 2 3 [2] : Total L).support,
              Bop q ((d 0 : ℕ) : ℤ)
                (MvPolynomial.coeff d (stageWordTotal q u 2 3 [2] : Total L)))
          = (q * u) • (Qop q u 2 3 (Qop q u 2 3 (1 : Lambda L))
              - Qop q u 4 6 (1 : Lambda L)) := by
  rw [lhsAt_two_three_singleton_iff_bop hq0 hu0 hq1 2 Θ,
    ← theta_completeHomog_two_apply_one_smul hΘ hv0 hv1, ← smul_neg]
  refine ⟨fun h => by rw [h], fun h => (smul_right_injective (Lambda L) hvn h).symm⟩

end HJO.Mellit
