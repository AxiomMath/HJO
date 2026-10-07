/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.DopWordMonomialExpansion
public import HJO.Shuffle.SweepPairIterate
public import HJO.Shuffle.SweepStageWordTwoThreeTwoValue

/-! # The two-part `hlhs` clause is the one-part family plus one `Θ`-free identity

This is the **join** of the two halves of the two-part clause at `(a,b) = (2,3)`, each proved
independently: the creation side of `HJO/Shuffle/DopWordMonomialExpansion.lean` and the sweep
side of `HJO/Shuffle/SweepPairIterate.lean`, which this file combines.

`HJO.Mellit.lhsAt_two_three_pair_iff` reduces `HJO.Mellit.LhsAt q u 2 3 Θ [A,B]` to

  `∑_{j≤B} c_j Θ(h_{B-j})(Θ(h_{A+j})(1)) = ct(d_-^2 G_{2,B}G_{1,A}(1))`,  `c_j = dispCoeff q j`,

on `q ≠ 0` alone. Two facts collapse the left-hand side onto the *one-part* family:
`HJO.Mellit.theta_completeHomog_mul_apply_one` (the nesting is `Θ` at an `h`-monomial, so the two
indices never interact) and `HJO.Mellit.theta_completeHomog_one`,
`HJO.Mellit.theta_completeHomog_two_smul` (the outer operators at `B ≤ 2` are the *explicit*
`-Q_{2,3}` and `qu(Q_{2,3}^2 - Q_{4,6})/(1+qu)`). On the other side
`HJO.Mellit.lhsAt_two_three_singleton_iff_bop` says the one-part clause at `[n]` is exactly
`Θ(h_n)(1) = HJO.Mellit.onePartSweepValue q u n`, an *explicit* element of `Λ`.

Putting the two together removes `Θ` from the two-part clause at `B ≤ 2` altogether.

## What is proved

* `HJO.Mellit.lhsAt_two_three_pair_of_singleton` — **the reduction, at every `(A,B)`.** If the
  one-part clause holds at each of `[A], [A+1], …, [A+B]`, then the two-part clause at `[A,B]`
  follows from the single identity

    `∑_{j≤B} c_j Θ(h_{B-j})(V_{A+j}) = ct(d_-^2 G_{2,B}G_{1,A}(1))`,   `V_n = onePartSweepValue n`,

  in which **no value of `Θ` at the vacuum occurs**: the only `Θ` left is the *operator*
  `Θ(h_{B-j})`, `B - j ≤ B`, read at the explicit sweep-side elements `V_{A+j}`. So the two-part
  family owes the one-part family and nothing else about `Θ` at the vacuum. An implication, not an
  equivalence — but `HJO.Mellit.lhsAt_two_three_pair_one_iff_of_singleton` records that at `B = 1`
  it is reversible, so nothing is weakened.

* `HJO.Mellit.lhsAt_two_three_pair_one_of_singleton` — **`B = 1`, entirely `Θ`-free.** At `B = 1`
  the only outer operator is `Θ(h_1) = -Q_{2,3}`, so the residual identity is

    `-Q_{2,3}(V_A) + (q^{-1}-1) V_{A+1} = ct(d_-^2 G_{2,1}G_{1,A}(1))`,

  with `Θ` absent from both sides. `HJO.Mellit.lhsAt_two_three_pair_one_of_singleton_bop` is the
  same with the right-hand side replaced by the double-`Bop` sum that
  `HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_pair_one` evaluates it to, so that every
  operator of the sweep is gone from the statement as well.

* `HJO.Mellit.forall_lhsAt_two_three_pair_one_of_singleton` — **the whole `[A,1]` family at once**,
  from two hypotheses stated as Lean propositions: the one-part family `∀ n, LhsAt q u 2 3 Θ [n]`,
  and the `Θ`-free residual family `∀ A`. Neither is discharged; the scope of each is spelled out at
  the declaration.

* `HJO.Mellit.lhsAt_two_three_pair_two_of_singleton` — **`B = 2`, `Θ`-free after clearing `1+qu`.**
  The outer operators are `Θ(h_2)`, `Θ(h_1)` and the identity, and `1 + qu` is carried on both sides
  rather than inverted.

* `HJO.Mellit.pairCreationSym` and `HJO.Mellit.lhsAt_two_three_pair_iff_pairCreationSym` — **the
  creation side of the two-part clause is one value of `Θ` at one element of `Λ`.** Because the
  nesting collapses, `∑_{j≤B} c_j Θ(h_{B-j})(Θ(h_{A+j})(1)) = Θ(P_{A,B})(1)` for the explicit,
  `Θ`-independent `P_{A,B} = ∑_{j≤B} c_j h_{B-j}h_{A+j}`. So the two-part clause has *the same
  shape* as the one-part clause `HJO.Mellit.lhsAt_two_three_singleton_iff`, with `h_A` replaced by
  `P_{A,B}`; the length of the composition is not visible on the creation side at all.

* **THE CONSISTENCY CHECK.** `HJO.Mellit.pair_one_residual_one` proves the `B = 1` residual at
  `A = 1` *without* using the decided `[1,1]` clause: it evaluates `V_1 = -Q_{2,3}(1)`
  (`HJO.Mellit.onePartSweepValue_one`), `(1+qu)V_2 = qu(Q_{2,3}^2(1) - Q_{4,6}(1))`
  (`HJO.Mellit.onePartSweepValue_two_smul`, from the nine-term degree-six value
  `HJO.Mellit.sum_bop_stageWordTotal_two_three_two`), and compares with the creation-versus-sweep
  identity `HJO.Mellit.qop_double_apply_one_two_three`. The arithmetic it exercises is
  `(q^{-1}-1)qu = u - qu`, giving `(qu+1) + (u - qu) = u + 1` and `-(u - qu) = u(q-1)` — the two
  coefficients of `Q_{2,3}^2(1)` and `Q_{4,6}(1)` in that identity. A sign in `dispCoeff`, an
  off-by-one in the `j`-range, or `Θ(h_1) = +Q_{2,3}` would each separate them.

  `HJO.Mellit.lhsAt_two_three_one_one_of_singleton_pair` then runs the general `[A,1]` theorem at
  `A = 1`, discharging its one-part hypotheses by
  `HJO.Mellit.lhsAt_two_three_one_of_axis` and `HJO.Mellit.lhsAt_two_three_two_of_axis` — so the
  decided `[2]` instance is exercised too —
  and arrives at the decided `[1,1]` clause. That the two statements are literally the same `Prop`
  is checked by `HJO.Mellit.lhsAt_two_three_one_one_of_singleton_pair_eq`, which is `rfl` against
  `HJO.Mellit.lhsAt_two_three_one_one`, hypothesis list included.

## What is NOT proved, with the quantifier named

**No new composition is decided here.** The residual identity is not discharged at any `A` other
than `A = 1`, for a reason on the *sweep* side that this file does not touch: the right-hand
side `ct(d_-^2 G_{2,1}G_{1,A}(1))` is evaluated by
`HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_pair_one` in terms of `HJO.Sweep.pairArgTwo`,
which still carries `T_1^{-1}`, and no closed form for `T_1^{-1}` on the monomials `y_1^ay_2^b` is
proved here. So:

* `∀ A`, the residual at `[A,1]` — **open**, blocked on `T_1^{-1}` (sweep side) for `A ≥ 2`.
* `A = 1` — the residual is proved here, and it is the only `A` at which it is.
* `(2,1)`, `(1,2)`, `(2,2)` — **still undecided.** `(2,1)` needs, beyond `T_1^{-1}`, the one-part
  value `V_3 = onePartSweepValue q u 3`, which no declaration supplies; the one-part clause
  family is itself decided only at `[1]` and `[2]`.
* `∀ B ≥ 3` — the reduction `HJO.Mellit.lhsAt_two_three_pair_of_singleton` holds, but its residual
  still contains the operator `Θ(h_{B-j})` for `B - j ≥ 3`, and no explicit form for `Θ(h_m)`,
  `m ≥ 3`, is available (`HJO.Mellit.theta_completeHomog_smul_eq_sum_qop` is a recursion, and
  unrolling it at `m = 3` needs `Q_{6,9}`).
* Nothing here says the two sides **differ** at any `(A,B)`; no comparison of two evaluated
  values is made beyond `(1,1)`, where they agree.

## Genericity

`HJO.Mellit.onePartSweepValue`, `HJO.Mellit.pairCreationSym`,
`HJO.Mellit.theta_pairCreationSym_apply_one`: **none**, the last being
`HJO.Mellit.theta_completeHomog_mul_apply_one` under a sum.

`HJO.Mellit.lhsAt_two_three_pair_iff_pairCreationSym`: `q ≠ 0`,
`HJO.Mellit.lhsAt_two_three_pair_iff`'s and nothing more; the parts need not be positive.

`HJO.Mellit.lhsAt_two_three_singleton_iff_onePartSweepValue`,
`HJO.Mellit.lhsAt_two_three_pair_of_singleton`: `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, verbatim
`HJO.Mellit.lhsAt_two_three_singleton_iff_bop`'s. Each is an inverse that becomes the zero map where
it fails — `(qu)^{-1}` of `HJO.Sweep.slopeOperator` and `(1-q)^{-1}` of `HJO.Sweep.zop` — so the
clause is false rather than vacuous there.

`HJO.Mellit.lhsAt_two_three_pair_one_of_singleton`,
`HJO.Mellit.lhsAt_two_three_pair_one_iff_of_singleton`,
`HJO.Mellit.lhsAt_two_three_pair_one_of_singleton_bop`,
`HJO.Mellit.forall_lhsAt_two_three_pair_one_of_singleton`: those plus `qu ≠ 0` and `qu ≠ 1`, which
are
`HJO.Sym.axisGen_one`'s and enter only through `HJO.Mellit.theta_completeHomog_one`. `q^{-1}` lives
inside `HJO.CreationSeeds.dispCoeff`, whose spelling `c_j = q^{-j} - q^{-(j-1)}` is the
unconditional one, and `M^{-1}` lives inside `HJO.Sym.Qop` and is carried, not cleared; so `M = 0`
is not excluded by these statements.

`HJO.Mellit.lhsAt_two_three_pair_two_of_singleton`: those plus `qu + 1 ≠ 0`, needed to cancel the
scalar `1 + qu` that `HJO.Mellit.theta_completeHomog_two_smul` carries. At `qu = -1` that
degree-two axis expansion is `0 = 0` and pins nothing, so the hypothesis is the route's and is real.

`HJO.Mellit.onePartSweepValue_one`, `HJO.Mellit.onePartSweepValue_two_smul`,
`HJO.Mellit.pair_one_residual_one`: `M = (1-q)(1-u) ≠ 0` — hence also `q ≠ 1` and `u ≠ 1` — for
`HJO.Sym.Qop`'s `M^{-1}` on the right-hand sides, together with `q ≠ 0`, `u ≠ 0`, `q ≠ 1`; and
`qu + 1 ≠ 0` for the last two, which is where `1 + qu` is cancelled.

`HJO.Mellit.lhsAt_two_three_one_one_of_singleton_pair`: verbatim
`HJO.Mellit.lhsAt_two_three_one_one`'s — `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, `u ≠ 1`, `qu ≠ 1`,
`qu + 1 ≠ 0` — deliberately, so that the `rfl` check against it can typecheck.

## References

Builds on `HJO.Sym.IsSlopeHom`, `HJO.Sym.Qop`, `HJO.Sym.completeHomog`, `HJO.Sym.Bop`,
`HJO.Mellit.stage`, `HJO.Mellit.lhsRewrite_sweepWitness` and
`HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc`.
-/

@[expose] public section

namespace HJO.Mellit

open Finset HJO.Sym HJO.Sweep HJO.CreationSeeds

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The one-part sweep value, named -/

/-- **The sweep side of the `hlhs` clause at the one-part composition `[A]`**,
`-∑_m B_m((G_A)_m)`: the Hall--Littlewood operators of `HJO.Sym.Bop` summed over the monomials of
the one-part stage word, with the sign that
`HJO.Mellit.lhsAt_two_three_singleton_iff_bop` puts there.

A name for an expression already in use, so that the two-part reduction below can be stated without
repeating it three times. Unconditional; at `A = 0` it is the value at `A = 1`, the power in
`HJO.Mellit.stage` being `A - 1` with truncated subtraction. -/
noncomputable def onePartSweepValue (q u : L) (A : ℕ) : Lambda L :=
  -∑ d ∈ (stageWordTotal q u 2 3 [A] : Total L).support,
      Bop q ((d 0 : ℕ) : ℤ) (MvPolynomial.coeff d (stageWordTotal q u 2 3 [A] : Total L))

/-- **The one-part clause at `[A]` is `Θ(h_A)(1) = V_A`.**
`HJO.Mellit.lhsAt_two_three_singleton_iff_bop` with the right-hand side named. The two statements
are definitionally the same. Genericity: `q ≠ 0`, `u ≠ 0`, `q ≠ 1`. -/
theorem lhsAt_two_three_singleton_iff_onePartSweepValue (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (A : ℕ) (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) :
    LhsAt q u 2 3 Θ [A] ↔ Θ (completeHomog L A) 1 = onePartSweepValue q u A :=
  lhsAt_two_three_singleton_iff_bop hq0 hu0 hq1 A Θ

/-! ### The creation side at `[A,B]` is one value of `Θ` at one element of `Λ` -/

/-- **The element of `Λ` whose `Θ`-value at the vacuum is the creation side at `[A,B]`:**
`P_{A,B} = ∑_{j≤B} c_j h_{B-j}h_{A+j}` with `c_j = HJO.CreationSeeds.dispCoeff q j`.

`Θ`-independent by construction, and explicit. Unconditional — `dispCoeff`'s spelling
`c_j = q^{-j} - q^{-(j-1)}` is the totalisation that survives `q = 0`. -/
noncomputable def pairCreationSym (q : L) (A B : ℕ) : Lambda L :=
  ∑ j ∈ range (B + 1), dispCoeff q j • (completeHomog L (B - j) * completeHomog L (A + j))

/-- **The nested creation side is a single value at `HJO.Mellit.pairCreationSym`:**
`Θ(P_{A,B})(1) = ∑_{j≤B} c_j Θ(h_{B-j})(Θ(h_{A+j})(1))`.

`HJO.Mellit.theta_completeHomog_mul_apply_one` termwise under the sum: the composite of the two
`h`-operators is the operator of the product, so the apparent nesting of the creation side is `Θ` at
an `h`-monomial, at the vacuum. **No hypothesis at all** — not on `q`, not on `u`, and `Θ` is only
asked to be an algebra homomorphism. -/
theorem theta_pairCreationSym_apply_one (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) (q : L)
    (A B : ℕ) :
    Θ (pairCreationSym q A B) 1
      = ∑ j ∈ range (B + 1), dispCoeff q j •
          Θ (completeHomog L (B - j)) (Θ (completeHomog L (A + j)) 1) := by
  rw [pairCreationSym, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, LinearMap.smul_apply, theta_completeHomog_mul_apply_one]

/-- **The two-part clause has the shape of the one-part clause.**

  `LhsAt q u 2 3 Θ [A,B] ↔ Θ(P_{A,B})(1) = ct(d_-^2 G_{2,B}G_{1,A}(1))`,

word for word `HJO.Mellit.lhsAt_two_three_singleton_iff` with `h_A` replaced by the explicit
`HJO.Mellit.pairCreationSym q A B`. So the *length* of the composition is invisible on the creation
side: what length two costs is a different element of `Λ`, not a different kind of datum. This is
`HJO.Mellit.lhsAt_two_three_pair_iff` composed with
`HJO.Mellit.theta_pairCreationSym_apply_one`, and it is an equivalence.

Genericity: `q ≠ 0`, `HJO.Mellit.lhsAt_two_three_pair_iff`'s and nothing else — not even positivity
of `A` and `B`. -/
theorem lhsAt_two_three_pair_iff_pairCreationSym (hq0 : q ≠ 0) (A B : ℕ)
    (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) :
    LhsAt q u 2 3 Θ [A, B] ↔
      Θ (pairCreationSym q A B) 1
        = MvPolynomial.constantCoeff (lowerRun q 2 (stageWordTotal q u 2 3 [A, B])) := by
  rw [lhsAt_two_three_pair_iff hq0 A B Θ, theta_pairCreationSym_apply_one]

/-! ### The two-part clause from the one-part family, at every `(A,B)` -/

/-- **THE REDUCTION: the two-part clause owes the one-part family and one residual identity.**

Given the one-part clause at each of `[A], [A+1], …, [A+B]`, the clause at `[A,B]` follows from

  `∑_{j≤B} c_j Θ(h_{B-j})(V_{A+j}) = ct(d_-^2 G_{2,B}G_{1,A}(1))`,
  `V_n = HJO.Mellit.onePartSweepValue q u n`.

**No value of `Θ` at the vacuum occurs in the residual.** That is the content: the creation side's
nested values `Θ(h_{B-j})(Θ(h_{A+j})(1))` are exactly the one-part clause's residuals fed into the
*operators* `Θ(h_m)`, `m ≤ B`, and those operators are `Θ`-free data at `m ≤ 2`
(`HJO.Mellit.theta_completeHomog_one`, `HJO.Mellit.theta_completeHomog_two_smul`). So the two-part
binder of `HJO.Mellit.LhsComputes` adds, over the one-part binder, an identity between two explicit
elements of `Λ` and nothing about `Θ` beyond what length one already asks.

Read in the other direction: the *defect* of the two-part clause is the image of the defects of the
one-part clauses under those operators, so at `B = 1` the reduction is reversible
(`HJO.Mellit.lhsAt_two_three_pair_one_iff_of_singleton`) and nothing is weakened by stating it as an
implication.

Genericity: `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, all three
`HJO.Mellit.lhsAt_two_three_singleton_iff_bop`'s; `A` and `B` are arbitrary and the parts need not
be positive. -/
theorem lhsAt_two_three_pair_of_singleton (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) (A B : ℕ)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hone : ∀ j ∈ range (B + 1), LhsAt q u 2 3 Θ [A + j])
    (hres : ∑ j ∈ range (B + 1), dispCoeff q j •
          Θ (completeHomog L (B - j)) (onePartSweepValue q u (A + j))
        = MvPolynomial.constantCoeff (lowerRun q 2 (stageWordTotal q u 2 3 [A, B]))) :
    LhsAt q u 2 3 Θ [A, B] := by
  refine (lhsAt_two_three_pair_iff hq0 A B Θ).2 ?_
  refine Eq.trans (Finset.sum_congr rfl fun j hj => ?_) hres
  rw [(lhsAt_two_three_singleton_iff_onePartSweepValue hq0 hu0 hq1 (A + j) Θ).1 (hone j hj)]

/-- **`B = 1`: the residual is `Θ`-free, at every `A`.**

From the one-part clause at `[A]` and at `[A+1]`, the clause at `[A,1]` follows from

  `-Q_{2,3}(V_A) + (q^{-1}-1) V_{A+1} = ct(d_-^2 G_{2,1}G_{1,A}(1))`,

in which `Θ` does not occur: the only outer operator at `B = 1` is `Θ(h_1) = -Q_{2,3}`
(`HJO.Mellit.theta_completeHomog_one`), the inner one is the identity because `h_0 = 1`, and both
`V_A` and the right-hand side are explicit elements of `Λ`. This is the whole two-part clause at an
**infinite** family of compositions, reduced to the one-part family plus an identity in `Λ`.

The residual is **not** discharged for any `A ≥ 2` here, and cannot be yet: the right-hand side is
evaluated by `HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_pair_one` in terms of
`HJO.Sweep.pairArgTwo`, which still carries `T_1^{-1}`. At `A = 1` it is
`HJO.Mellit.pair_one_residual_one`.

Genericity: `q ≠ 0`, `u ≠ 0`, `q ≠ 1` for the one-part equivalence; `qu ≠ 0`, `qu ≠ 1` for
`Θ(h_1) = -Q_{2,3}`. Nothing excludes `qu = -1` or `M = 0`: `q^{-1}` is inside
`HJO.CreationSeeds.dispCoeff`'s unconditional spelling and `M^{-1}` inside `HJO.Sym.Qop`, both
carried rather than cleared. -/
theorem lhsAt_two_three_pair_one_of_singleton (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1) {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom 2 3 q u Θ) (A : ℕ)
    (hA : LhsAt q u 2 3 Θ [A]) (hA1 : LhsAt q u 2 3 Θ [A + 1])
    (hres : -Qop q u 2 3 (onePartSweepValue q u A)
          + dispCoeff q 1 • onePartSweepValue q u (A + 1)
        = MvPolynomial.constantCoeff (lowerRun q 2 (stageWordTotal q u 2 3 [A, 1]))) :
    LhsAt q u 2 3 Θ [A, 1] := by
  refine lhsAt_two_three_pair_of_singleton hq0 hu0 hq1 A 1 (fun j hj => ?_) ?_
  · have hj' : j = 0 ∨ j = 1 := by
      have := Finset.mem_range.1 hj; omega
    rcases hj' with h | h
    · simpa only [h, Nat.add_zero] using hA
    · simpa only [h] using hA1
  · rw [Finset.sum_range_succ, Finset.sum_range_one, dispCoeff_zero, one_smul, Nat.add_zero,
      Nat.sub_zero, Nat.sub_self, CopPower.completeHomog_zero, map_one, Module.End.one_apply,
      theta_completeHomog_one hΘ hv0 hv1, LinearMap.neg_apply]
    exact hres

/-- **Nothing is weakened at `B = 1`: the residual is necessary as well as sufficient.**

Given the one-part clause at `[A]` and `[A+1]`, the two-part clause at `[A,1]` is *equivalent*
to the `Θ`-free residual. So `HJO.Mellit.lhsAt_two_three_pair_one_of_singleton` is not a lossy
sufficient
condition dressed up as a reduction: modulo the one-part family, the residual identity **is** the
clause at `[A,1]`, and a proof of the clause would yield the identity back.

Genericity: verbatim `HJO.Mellit.lhsAt_two_three_pair_one_of_singleton`'s. -/
theorem lhsAt_two_three_pair_one_iff_of_singleton (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1) {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom 2 3 q u Θ) (A : ℕ)
    (hA : LhsAt q u 2 3 Θ [A]) (hA1 : LhsAt q u 2 3 Θ [A + 1]) :
    LhsAt q u 2 3 Θ [A, 1] ↔
      -Qop q u 2 3 (onePartSweepValue q u A)
          + dispCoeff q 1 • onePartSweepValue q u (A + 1)
        = MvPolynomial.constantCoeff (lowerRun q 2 (stageWordTotal q u 2 3 [A, 1])) := by
  have hsum : ∑ j ∈ range (1 + 1), dispCoeff q j •
        Θ (completeHomog L (1 - j)) (Θ (completeHomog L (A + j)) 1)
      = -Qop q u 2 3 (onePartSweepValue q u A)
        + dispCoeff q 1 • onePartSweepValue q u (A + 1) := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    rw [(lhsAt_two_three_singleton_iff_onePartSweepValue hq0 hu0 hq1 (A + 1) Θ).1 hA1]
    simp only [dispCoeff_zero, one_smul, Nat.add_zero, Nat.sub_zero, Nat.sub_self,
      CopPower.completeHomog_zero, map_one, Module.End.one_apply]
    rw [(lhsAt_two_three_singleton_iff_onePartSweepValue hq0 hu0 hq1 A Θ).1 hA,
      theta_completeHomog_one hΘ hv0 hv1, LinearMap.neg_apply]
  rw [lhsAt_two_three_pair_iff hq0 A 1 Θ, hsum]

/-- **`B = 1` with every operator of the sweep gone as well.**

`HJO.Mellit.lhsAt_two_three_pair_one_of_singleton` with the right-hand side of its residual replaced
by the value `HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_pair_one` computes it to:

  `-Q_{2,3}(V_A) + (q^{-1}-1)V_{A+1}
     = (qu)^{-1}\frac{q^2}{1-q} ∑_{(m,n)}∑_j B_{j+1}(B_m(zDefect_n(P_{mn})_j))`,

the sums over the monomials of `HJO.Sweep.pairArgTwo q u A`. Both sides are now `Λ`-level
expressions in `HJO.Sym.Bop` alone — no train, no stage, no replication family, no slope
homomorphism — and what stands between this and a decision at every `A` is the closed form of
`T_1^{-1}` inside `HJO.Sweep.pairArgTwo`, nothing on the creation side.

Genericity: verbatim `HJO.Mellit.lhsAt_two_three_pair_one_of_singleton`'s; the sweep evaluation it
cites is unconditional. -/
theorem lhsAt_two_three_pair_one_of_singleton_bop (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1) {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom 2 3 q u Θ) (A : ℕ)
    (hA : LhsAt q u 2 3 Θ [A]) (hA1 : LhsAt q u 2 3 Θ [A + 1])
    (hres : -Qop q u 2 3 (onePartSweepValue q u A)
          + dispCoeff q 1 • onePartSweepValue q u (A + 1)
        = ((q * u)⁻¹ * (q ^ 2 / (1 - q))) •
            ∑ d ∈ (pairArgTwo q u A).support,
              ∑ e ∈ (zDefect q u (d 1) (MvPolynomial.coeff d (pairArgTwo q u A))).support,
                Bop q (((e 0 + 1 : ℕ) : ℤ))
                  (Bop q ((d 0 : ℕ) : ℤ)
                    (MvPolynomial.coeff e (zDefect q u (d 1)
                      (MvPolynomial.coeff d (pairArgTwo q u A)))))) :
    LhsAt q u 2 3 Θ [A, 1] :=
  lhsAt_two_three_pair_one_of_singleton hq0 hu0 hq1 hv0 hv1 hΘ A hA hA1
    (by rw [hres, constantCoeff_lowerRun_two_stageWordTotal_pair_one])

/-- **The `[A,1]` family of the `hlhs` clause, at EVERY `A`, from two named hypotheses.**

The two hypotheses, both stated here as Lean propositions and neither about `Θ` at a composition of
length two:

* `hone` — the **one-part family** of the clause, `∀ n, LhsAt q u 2 3 Θ [n]`. Decided at `n = 1` and
  `n = 2` (`HJO.Mellit.lhsAt_two_three_one_of_axis`, `HJO.Mellit.lhsAt_two_three_two_of_axis`); open
  at every `n ≥ 3`, where `HJO.Mellit.lhsAt_two_three_singleton_iff_bop` is a decision procedure per
  fixed `n` and the `e`-expansion of the value grows (2, 9, 26 monomials at `n = 1, 2, 3`).
* `hres` — the **`Θ`-free residual family**, `∀ A`, an identity between two explicit elements of
  `Λ`. Proved here at `A = 1` only (`HJO.Mellit.pair_one_residual_one`); at `A ≥ 2` its right-hand
  side is
  not evaluated, because `HJO.Sweep.pairArgTwo` still carries `T_1^{-1}`.

So the *scope* of what is delivered is: the entire `[A,1]` family of the two-part binder costs the
one-part binder plus a family of identities in `Λ` with no slope homomorphism in it. The conclusion
is an infinite family of clause instances; the hypotheses are not discharged.

Genericity: `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, `qu ≠ 0`, `qu ≠ 1`. -/
theorem forall_lhsAt_two_three_pair_one_of_singleton (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1) {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom 2 3 q u Θ) (hone : ∀ n : ℕ, LhsAt q u 2 3 Θ [n])
    (hres : ∀ A : ℕ, -Qop q u 2 3 (onePartSweepValue q u A)
          + dispCoeff q 1 • onePartSweepValue q u (A + 1)
        = MvPolynomial.constantCoeff (lowerRun q 2 (stageWordTotal q u 2 3 [A, 1]))) :
    ∀ A : ℕ, LhsAt q u 2 3 Θ [A, 1] := fun A =>
  lhsAt_two_three_pair_one_of_singleton hq0 hu0 hq1 hv0 hv1 hΘ A (hone A) (hone (A + 1)) (hres A)

/-- **`B = 2`: the residual is `Θ`-free after clearing `1 + qu`, at every `A`.**

From the one-part clause at `[A]`, `[A+1]` and `[A+2]`, the clause at `[A,2]` follows from

  `qu (Q_{2,3}^2 - Q_{4,6})(V_A) + (1+qu)( c_1·(-Q_{2,3}(V_{A+1})) + c_2·V_{A+2} )
     = (1+qu) ct(d_-^2 G_{2,2}G_{1,A}(1))`,

the three outer operators of `HJO.Mellit.theta_copComp_pair_two_apply_one` being `Θ(h_2)`, `Θ(h_1)`
and the identity, and `HJO.Mellit.theta_completeHomog_two_smul` making the first explicit with
`1 + qu` carried. A second infinite family, on the same footing as `B = 1`.

**Unlike the `B = 1` family this has no independent check**: no `[A,2]` composition is decided, so
nothing here is checked against a known value. What it shares with `B = 1` is the residual's
derivation from `HJO.Mellit.lhsAt_two_three_pair_of_singleton`, which the `B = 1` check exercises.

Genericity: `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, `qu ≠ 0`, `qu ≠ 1`, and `qu + 1 ≠ 0` to cancel the carried
`1 + qu`; at `qu = -1` the degree-two axis expansion is `0 = 0` and determines nothing, so that
hypothesis is real and not decoration. -/
theorem lhsAt_two_three_pair_two_of_singleton (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1) (hvm : q * u + 1 ≠ 0)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom 2 3 q u Θ) (A : ℕ)
    (hA : LhsAt q u 2 3 Θ [A]) (hA1 : LhsAt q u 2 3 Θ [A + 1])
    (hA2 : LhsAt q u 2 3 Θ [A + 2])
    (hres : (q * u) • (Qop q u 2 3 (Qop q u 2 3 (onePartSweepValue q u A))
            - Qop q u 4 6 (onePartSweepValue q u A))
          + (q * u + 1) • (dispCoeff q 1 • -Qop q u 2 3 (onePartSweepValue q u (A + 1))
              + dispCoeff q 2 • onePartSweepValue q u (A + 2))
        = (q * u + 1) •
            MvPolynomial.constantCoeff (lowerRun q 2 (stageWordTotal q u 2 3 [A, 2]))) :
    LhsAt q u 2 3 Θ [A, 2] := by
  refine lhsAt_two_three_pair_of_singleton hq0 hu0 hq1 A 2 (fun j hj => ?_) ?_
  · have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by
      have := Finset.mem_range.1 hj; omega
    rcases hj' with h | h | h
    · simpa only [h, Nat.add_zero] using hA
    · simpa only [h] using hA1
    · simpa only [h] using hA2
  · have h2 := congrArg (fun T : Module.End L (Lambda L) => T (onePartSweepValue q u A))
      (theta_completeHomog_two_smul hΘ hv0 hv1)
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply] at h2
    refine smul_right_injective (Lambda L) hvm ?_
    dsimp only
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      dispCoeff_zero, one_smul, Nat.add_zero, Nat.sub_zero, show (2 : ℕ) - 1 = 1 from rfl,
      Nat.sub_self, CopPower.completeHomog_zero, map_one, Module.End.one_apply,
      theta_completeHomog_one hΘ hv0 hv1, LinearMap.neg_apply, smul_add, smul_add, h2, ← hres]
    module

/-! ### Consistency check: the decided `[1,1]` instance re-derived through the general route -/

/-- **`V_1 = -Q_{2,3}(1)`.** The one-part sweep value at `A = 1`:
`HJO.Mellit.sum_bop_stageWordTotal_two_three_one` evaluates the Hall--Littlewood sum as
`-e_1e_2 + (1-q-u)e_3`, and `HJO.Mellit.qop_two_three_apply_one` says that element is `Q_{2,3}(1)`.

Genericity: `M = (1-q)(1-u) ≠ 0` for `HJO.Sym.Qop`'s `M^{-1}`, plus `q ≠ 0`, `u ≠ 0`, `q ≠ 1` for
the seed. -/
theorem onePartSweepValue_one (hM : (1 - q) * (1 - u) ≠ 0) (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) : onePartSweepValue q u 1 = -Qop q u 2 3 (1 : Lambda L) := by
  rw [onePartSweepValue, sum_bop_stageWordTotal_two_three_one hM hq0 hu0 hq1,
    qop_two_three_apply_one hM]

/-- **`(1+qu)V_2 = qu(Q_{2,3}(Q_{2,3}(1)) - Q_{4,6}(1))`**, the one-part sweep value at `A = 2`
identified with the creation-side combination — **without any slope homomorphism.**

Both sides are computed explicitly over the nine degree-six `e`-monomials:
`HJO.Mellit.sum_bop_stageWordTotal_two_three_two` on the left,
`HJO.Mellit.qop_two_three_apply_qop_two_three_apply_one` and `HJO.Mellit.qop_four_six_apply_one` on
the right, and the comparison is one `ring` call. This is the `Θ`-free content of the decided `[2]`
clause, extracted so that the `[1,1]` check below does not have to go through `Θ` at all — which is
what keeps that check non-circular.

Genericity: `M ≠ 0`, `q ≠ 0`, `u ≠ 0`, `q ≠ 1`; `1 + qu` is carried, not inverted. -/
theorem onePartSweepValue_two_smul (hM : (1 - q) * (1 - u) ≠ 0) (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) :
    (q * u + 1) • onePartSweepValue q u 2
      = (q * u) • (Qop q u 2 3 (Qop q u 2 3 (1 : Lambda L)) - Qop q u 4 6 (1 : Lambda L)) := by
  rw [onePartSweepValue, sum_bop_stageWordTotal_two_three_two hq0 hu0 hq1,
    qop_two_three_apply_qop_two_three_apply_one hM, qop_four_six_apply_one hM]
  simp only [smul_neg, MvPolynomial.smul_eq_C_mul, map_add, map_sub, map_neg, map_mul, map_one,
    map_pow, map_ofNat]
  ring

/-- **THE CONSISTENCY CHECK: the `B = 1` residual holds at `A = 1`.**

  `-Q_{2,3}(V_1) + (q^{-1}-1)V_2 = ct(d_-^2 G_{2,1}G_{1,1}(1))`.

Proved **without the decided `[1,1]` clause and without any `Θ`**, so it is a genuine check on the
shape of the general residual rather than a restatement: `V_1 = -Q_{2,3}(1)` and
`(1+qu)V_2 = qu(Q_{2,3}^2(1) - Q_{4,6}(1))` come from the two one-part sweep values, and the
target comes from the creation-versus-sweep identity
`HJO.Mellit.qop_double_apply_one_two_three`.

Multiplying by `1 + qu`, the two coefficients that have to come out are

  `(qu+1) + (q^{-1}-1)qu = u+1`   and   `-(q^{-1}-1)qu = u(q-1)`,

which is where `q ≠ 0` is spent (`(q^{-1}-1)qu = u - qu`) and the only place. An off-by-one in the
`j`-range of `HJO.Mellit.lhsAt_two_three_pair_iff`, a sign in `HJO.CreationSeeds.dispCoeff`, or
`Θ(h_1) = +Q_{2,3}` instead of `-Q_{2,3}` would each leave this unprovable.

Genericity: `M ≠ 0` — hence also `u ≠ 1` — with `q ≠ 0`, `u ≠ 0`, `q ≠ 1` and `qu + 1 ≠ 0` for the
cancellation. -/
theorem pair_one_residual_one (hM : (1 - q) * (1 - u) ≠ 0) (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) (hvm : q * u + 1 ≠ 0) :
    -Qop q u 2 3 (onePartSweepValue q u 1) + dispCoeff q 1 • onePartSweepValue q u 2
      = MvPolynomial.constantCoeff (lowerRun q 2 (stageWordTotal q u 2 3 [1, 1])) := by
  have hcoef : (q⁻¹ - 1) * (q * u) = u - q * u := by
    have hinv : q⁻¹ * q = 1 := inv_mul_cancel₀ hq0
    linear_combination u * hinv
  refine smul_right_injective (Lambda L) hvm ?_
  dsimp only
  rw [smul_add, onePartSweepValue_one hM hq0 hu0 hq1, map_neg, neg_neg,
    smul_comm (q * u + 1) (dispCoeff q 1), onePartSweepValue_two_smul hM hq0 hu0 hq1,
    ← qop_double_apply_one_two_three hM hq0 hu0 hq1, dispCoeff_one, smul_smul, hcoef]
  module

/-- **The decided `[1,1]` clause, re-derived *through* the general `[A,1]` reduction.**

`HJO.Mellit.lhsAt_two_three_pair_one_of_singleton` at `A = 1`, with its three hypotheses discharged:
the one-part clause at `[1]` by `HJO.Mellit.lhsAt_two_three_one_of_axis`, the one-part clause at
`[1+1] = [2]` by `HJO.Mellit.lhsAt_two_three_two_of_axis` — so the decided `[2]` instance is
exercised as well — and the residual by `HJO.Mellit.pair_one_residual_one`.

The hypothesis list is chosen to be verbatim `HJO.Mellit.lhsAt_two_three_one_one`'s (`M ≠ 0` and
`qu ≠ 0` are derived inside), so that
`HJO.Mellit.lhsAt_two_three_one_one_of_singleton_pair_eq` can compare the two by `rfl`. -/
theorem lhsAt_two_three_one_one_of_singleton_pair (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (hu1 : u ≠ 1) (hv1 : q * u ≠ 1) (hvm : q * u + 1 ≠ 0)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom 2 3 q u Θ) :
    LhsAt q u 2 3 Θ [1, 1] := by
  have hM : (1 - q) * (1 - u) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr (Ne.symm hq1)) (sub_ne_zero.mpr (Ne.symm hu1))
  have hv0 : q * u ≠ 0 := mul_ne_zero hq0 hu0
  exact lhsAt_two_three_pair_one_of_singleton hq0 hu0 hq1 hv0 hv1 hΘ 1
    (lhsAt_two_three_one_of_axis hM hq0 hu0 hq1 hv0 hv1 hΘ)
    (by simpa only [show (1 : ℕ) + 1 = 2 from rfl] using
      lhsAt_two_three_two_of_axis hM hq0 hu0 hq1 hv0 hv1 hvm hΘ)
    (pair_one_residual_one hM hq0 hu0 hq1 hvm)

/-- **The general route and the proved `[1,1]` clause state the same `Prop`.** `rfl` between the two
proofs typechecks only if the statements — and the hypothesis lists — are identical. The left-hand
route is this file's reduction of the two-part clause to the one-part family; the right-hand one is
`HJO.Mellit.lhsAt_two_three_one_one`, proved from the degree-two axis expansion of
`e_2` with no one-part clause anywhere in it. -/
theorem lhsAt_two_three_one_one_of_singleton_pair_eq (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (hu1 : u ≠ 1) (hv1 : q * u ≠ 1) (hvm : q * u + 1 ≠ 0)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom 2 3 q u Θ) :
    lhsAt_two_three_one_one_of_singleton_pair hq0 hu0 hq1 hu1 hv1 hvm hΘ
      = lhsAt_two_three_one_one hq0 hu0 hq1 hu1 hv1 hvm hΘ := rfl

end HJO.Mellit

end
