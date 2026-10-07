/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.AxisNewtonCompleteHomog
public import HJO.Shuffle.MellitTwoPartTwoThreeClause

/-! # The creation side of the `hlhs` clause at a one-part composition: `Θ(h_A)(1)` at `(2,3)`

`HJO.Mellit.lhsAt_two_three_singleton_iff_bop` (`HJO/Shuffle/SweepReplicatedIterate.lean`)
proves that the `hlhs` clause at the one-part composition `[A]` and `(a,b) = (2,3)` is *exactly*

  `Θ(h_A)(1) = -∑_m B_m((G_A)_m)`,

so with the sweep side evaluated the whole residual is the single creation-side value `Θ(h_A)(1)`.
This file computes it.

## What `Θ(h_A)(1)` is

A slope homomorphism of `HJO.Sym.IsSlopeHom` is prescribed only on the axis generators of
`HJO.Sym.axisGen`, so `Θ(h_A)` is whatever the expansion of `h_A` on `U_1, …, U_A` makes it. Two
inputs turn that into a computation:

* `HJO.Sym.completeHomog_smul_eq_sum_axisGen` — Newton's identity for the axis generators,
  `(1 - v^A) h_A = (v-1)v^{A-1} ∑_{s=1}^{A} h_{A-s} U_s` with `v = qu`.
* `HJO.Sym.IsSlopeHom` itself, which sends `U_s` to `Q_{2s,3s}`.

Pushing the first along `Θ` gives `HJO.Mellit.theta_completeHomog_smul_eq_sum_qop`, and evaluating
at the vacuum gives `HJO.Mellit.theta_completeHomog_apply_one_smul_eq_sum_qop`:

  `(1 - v^A) Θ(h_A)(1) = (v-1)v^{A-1} ∑_{s=1}^{A} Θ(h_{A-s})(Q_{2s,3s}(1))`.

**That is the answer in a form usable at every `A`**: a one-step recursion in `A` whose only inputs
are the vacuum values `Q_{2s,3s}(1)` — each given in closed form at every `s ≥ 1` by
`HJO.Sym.qop_two_three_axis_eq_ladder` — and the operators `Θ(h_{A-s})` the recursion has already
produced. There is no closed form to be had: the expansion of `h_A` on the axis generators has one
monomial per partition of `A`, so the recursion is the statement, not a step towards one.

## `A = 2`, in closed form

At `A = 2` the recursion has two terms, and both `Q`-values are known:
`HJO.Sym.qop_two_three_apply_qop_two_three_apply_one` and `HJO.Sym.qop_four_six_apply_one`. So the
value is explicit:

  `(1 + qu) Θ(h_2)(1) = qu (Q_{2,3}(Q_{2,3}1) - Q_{4,6}(1))`

(`HJO.Mellit.theta_completeHomog_two_apply_one_smul`), and
`HJO.Mellit.theta_completeHomog_two_apply_one` writes the right-hand side out over the nine
degree-six `e`-monomials
`e_1^3e_3, e_1^2e_2^2, e_1^2e_4, e_1e_2e_3, e_1e_5, e_2^3, e_2e_4, e_3^2, e_6`. **No monomial's
coefficient vanishes**, and the nine coefficients carry `6, 2, 14, 16, 35, 6, 27, 19, 33` terms in
`(q,u)` — `158` in all, of total degree up to `11`.

This is the first one-part instance of the creation side past the base case. It does **not** by
itself decide the clause at `[2]`: the equivalence of
`HJO.Mellit.lhsAt_two_three_singleton_iff_bop` needs the sweep side `∑_m B_m((G_2)_m)` in the same
nine monomials, which is computed in `HJO/Shuffle/SweepStageWordTwoThreeTwoValue.lean`. What is
supplied here is one of its two sides, in a basis the other can be compared against term by term.

## Consistency check at `A = 1`

`HJO.Mellit.theta_completeHomog_one_apply_one` derives `Θ(h_1)(1) = e_1e_2 - (1-q-u)e_3` from the
axis route alone — `h_1 = -U_1` by `HJO.Sym.axisGen_one`, then
`HJO.Sym.qop_two_three_apply_one`. That is the same value
`HJO.Mellit.theta_completeHomog_one_of_slopeHom`
(`HJO/Shuffle/SweepReplicatedIterate.lean`) obtains from the *sweep* side of the decided
singleton clause. The two routes share nothing: one reads the axis prescription, the other runs the
Hall--Littlewood sum of `HJO.Sym.Bop` on the stage word. Their agreement is a check on this file's
normalisation, and a sign lost anywhere in the axis expansion would break it.

## Genericity

Every statement here carries `qu ≠ 0` and `qu ≠ 1`, which at `v = qu` are
`HJO.Sym.completeHomog_smul_eq_sum_axisGen`'s `v ≠ 0` and `v ≠ 1` — the
inverse-becomes-zero hazard of `HJO.Sym.axisGen`'s normalising scalar `v/(v-1)`: in a field
`0⁻¹ = 0`, so at `qu = 1` that scalar collapses and every `U_k` is `0` (`HJO.Sym.axisGen_eq_zero`),
and there the statements are false rather than vacuous. `qu ≠ 0` gives `q ≠ 0` and `u ≠ 0`.

The statements naming a `Q`-value in closed form carry in addition `M = (1-q)(1-u) ≠ 0`, which is
`HJO.Sym.Qop`'s `M^{-1}`, the same hazard: at `M = 0` the slope operators are the zero map by
totalisation and the closed forms read `0 = 0`.

`HJO.Mellit.theta_completeHomog_two_apply_one_of_ne_neg_one` carries `qu ≠ -1` as well, and
**nothing else does**: the scalar `1 + qu` is never inverted in the statements above, so it is only
the form solved for `Θ(h_2)(1)` that excludes `qu = -1`. At `qu = -1` the degree-two expansion
`(v+1)h_2 = v(U_1^2 - U_2)` degenerates and `h_2` is not determined by `U_1, U_2` — which is a fact
about the axis generators at a second root of unity, not an artefact.

A result at `a = 1`, `q = 1` or `u = 1` would settle nothing about the clause; `(2,3)` is coprime
with `1 < a < b`, and `q = 1` is excluded above while `u = 1` is excluded by `M ≠ 0` wherever a
closed form is named.

## Relation to the `hlhs` clause

These are the values of `HJO.Sym.IsSlopeHom` on `HJO.Sym.completeHomog`; the `hlhs` clause is
the *equation* between this value and the sweep side, and that equation is the subject of
`HJO.Mellit.lhsAt_two_three_singleton_iff_bop`.

## References

The file evaluates `HJO.Sym.IsSlopeHom` on `HJO.Sym.completeHomog` through `HJO.Sym.axisGen`,
`HJO.Sym.Qop`, `HJO.Sym.elemSymm`, `HJO.Sym.Bop` and
`HJO.Sym.sum_alternating_pow_completeHomog_mul_elemSymm`, towards
`HJO.Mellit.lhsRewrite_sweepWitness`.
-/

@[expose] public section

-- Every exponent written as a numeral in this file is a natural number. Saying so up front lets
-- each `x ^ n` resolve `HPow _ ℕ _` at once instead of retrying instance resolution for the
-- pending numeral type until defaulting, which dominated elaboration here. The elaborated terms
-- are the ones the default instance would produce.
local macro_rules | `($x ^ $n:num) => `(rightact% HPow.hPow $x ($n : ℕ))

namespace HJO.Mellit

open HJO.Sym Finset

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The recursion, transported along `Θ` -/

/-- **`(1 - v^A) Θ(h_A) = (v-1)v^{A-1} ∑_{s=1}^{A} Θ(h_{A-s}) Q_{2s,3s}`, `v = qu`.**

`HJO.Sym.completeHomog_smul_eq_sum_axisGen` pushed along the algebra homomorphism `Θ`: the product
`h_{A-s}U_s` becomes the *composite* `Θ(h_{A-s})Q_{2s,3s}` of endomorphisms, and
`HJO.Sym.IsSlopeHom` is what evaluates the second factor. Both scalars ride along unchanged, neither
being inverted.

Genericity: `qu ≠ 0`, `qu ≠ 1`, the axis identity's. -/
theorem theta_completeHomog_smul_eq_sum_qop {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom 2 3 q u Θ) (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1) (A : ℕ) :
    (1 - (q * u) ^ A) • Θ (completeHomog L A)
      = ((q * u - 1) * (q * u) ^ (A - 1)) •
          ∑ s ∈ range A,
            Θ (completeHomog L (A - (s + 1))) * Qop q u (2 * (s + 1)) (3 * (s + 1)) := by
  have h := congrArg Θ (completeHomog_smul_eq_sum_axisGen (L := L) hv0 hv1 A)
  rw [map_smul, map_smul, map_sum] at h
  rw [h]
  refine congrArg _ (Finset.sum_congr rfl fun s _ => ?_)
  rw [map_mul, hΘ (s + 1) (Nat.succ_pos s)]

/-- **The recursion at the vacuum**, which is the form the clause needs:

  `(1 - v^A) Θ(h_A)(1) = (v-1)v^{A-1} ∑_{s=1}^{A} Θ(h_{A-s})(Q_{2s,3s}(1))`.

Every input is a vacuum value of a slope operator, and
`HJO.Sym.qop_two_three_axis_eq_ladder` gives each `Q_{2s,3s}` in closed form as a word in `D_1` and
`D_2` at every `s ≥ 1` with no case split. So the right-hand side is computable at each `A` from the
operators the recursion has already produced.

Genericity: `qu ≠ 0`, `qu ≠ 1`. -/
theorem theta_completeHomog_apply_one_smul_eq_sum_qop
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom 2 3 q u Θ) (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1) (A : ℕ) :
    (1 - (q * u) ^ A) • Θ (completeHomog L A) 1
      = ((q * u - 1) * (q * u) ^ (A - 1)) •
          ∑ s ∈ range A,
            Θ (completeHomog L (A - (s + 1))) (Qop q u (2 * (s + 1)) (3 * (s + 1)) 1) := by
  have h := congrArg (fun T : Module.End L (Lambda L) => T (1 : Lambda L))
    (theta_completeHomog_smul_eq_sum_qop hΘ hv0 hv1 A)
  simpa only [LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply] using h

/-! ### Consistency check at `A = 1` -/

/-- **`Θ(h_1) = -Q_{2,3}`.** `h_1 = e_1 = -U_1` (`HJO.Sym.axisGen_one`), and `HJO.Sym.IsSlopeHom`
sends `U_1` to `Q_{2,3}`. Genericity: `qu ≠ 0`, `qu ≠ 1`. -/
theorem theta_completeHomog_one {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom 2 3 q u Θ) (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1) :
    Θ (completeHomog L 1) = -Qop q u 2 3 := by
  rw [show completeHomog L 1 = -axisGen (q * u) 1 from by
      rw [axisGen_one hv0 hv1, neg_neg, CopPower.completeHomog_one, CopPower.powerSum_one,
        elemSymm_one_eq_X],
    map_neg, hΘ 1 one_pos]

/-- **`Θ(h_1)(1) = e_1e_2 - (1-q-u)e_3`, by the axis route.**

This is the check on the whole file. `HJO.Mellit.theta_completeHomog_one_of_slopeHom`
(`HJO/Shuffle/SweepReplicatedIterate.lean`) obtains the same value from the *sweep* side of
the decided singleton clause — the Hall--Littlewood sum of `HJO.Sym.Bop` over the monomials of the
one-part stage word — and this proof never touches that side: it reads `h_1 = -U_1` off
`HJO.Sym.axisGen` and `Q_{2,3}(1)` off `HJO.Sym.qop_two_three_apply_one`. A sign lost in the axis
expansion would separate the two values.

Genericity: `M ≠ 0` for `HJO.Sym.Qop`'s `M^{-1}` — so also `q ≠ 1` and `u ≠ 1` — together with
`qu ≠ 0` and `qu ≠ 1`. -/
theorem theta_completeHomog_one_apply_one (hM : (1 - q) * (1 - u) ≠ 0)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom 2 3 q u Θ) (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1) :
    Θ (completeHomog L 1) 1 = elemSymm L 1 * elemSymm L 2 - (1 - q - u) • elemSymm L 3 := by
  rw [theta_completeHomog_one hΘ hv0 hv1, LinearMap.neg_apply, qop_two_three_apply_one hM]
  abel

/-! ### `A = 2` -/

/-- **`(1 + qu) Θ(h_2) = qu (Q_{2,3}^2 - Q_{4,6})`.**

`HJO.Sym.completeHomog_two_smul_eq_axisGen` pushed along `Θ`: `U_1^2` becomes `Q_{2,3}^2` — the
composite of the *same* operator with itself, `Θ` being multiplicative — and `U_2` becomes the
operator at the **doubled** slope `Q_{4,6}`, which is where `h_2` genuinely reads more than the
clause at `[1]` does.

The scalar `1 + qu` is not inverted. Genericity: `qu ≠ 0`, `qu ≠ 1`. -/
theorem theta_completeHomog_two_smul {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom 2 3 q u Θ) (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1) :
    (q * u + 1) • Θ (completeHomog L 2)
      = (q * u) • (Qop q u 2 3 * Qop q u 2 3 - Qop q u 4 6) := by
  have h := congrArg Θ (completeHomog_two_smul_eq_axisGen (L := L) hv0 hv1)
  rw [map_smul, map_smul, map_sub, map_pow, hΘ 1 one_pos, hΘ 2 two_pos] at h
  rw [h]
  norm_num [sq]

/-- **`(1 + qu) Θ(h_2)(1) = qu (Q_{2,3}(Q_{2,3}1) - Q_{4,6}(1))`** — the creation-side residual of
the clause at `[2]`, reduced to two known vacuum values.

Genericity: `qu ≠ 0`, `qu ≠ 1`; no inverse, and in particular no exclusion at `qu = -1`. -/
theorem theta_completeHomog_two_apply_one_smul {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom 2 3 q u Θ) (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1) :
    (q * u + 1) • Θ (completeHomog L 2) 1
      = (q * u) • (Qop q u 2 3 (Qop q u 2 3 (1 : Lambda L)) - Qop q u 4 6 (1 : Lambda L)) := by
  have h := congrArg (fun T : Module.End L (Lambda L) => T (1 : Lambda L))
    (theta_completeHomog_two_smul hΘ hv0 hv1)
  simpa only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply] using h

/-- **`Θ(h_2)(1)`, solved for.** `HJO.Mellit.theta_completeHomog_two_apply_one_smul` divided by
`1 + qu`.

This is the **only** statement in the file excluding `qu = -1`, and the exclusion is real rather
than cosmetic: at `qu = -1` the degree-two axis expansion `(v+1)h_2 = v(U_1^2 - U_2)` has zero on
the left, so `h_2` is not determined by `U_1` and `U_2` and there is nothing to solve for. In a
field `0⁻¹ = 0`, so writing `(1+qu)^{-1}` without the hypothesis would make the right-hand side the
zero element and the statement false.

Genericity: `qu ≠ 0`, `qu ≠ 1`, `qu ≠ -1`. -/
theorem theta_completeHomog_two_apply_one_of_ne_neg_one {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom 2 3 q u Θ) (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1) (hvn : q * u + 1 ≠ 0) :
    Θ (completeHomog L 2) 1
      = ((q * u + 1)⁻¹ * (q * u)) •
          (Qop q u 2 3 (Qop q u 2 3 (1 : Lambda L)) - Qop q u 4 6 (1 : Lambda L)) := by
  rw [mul_smul, ← theta_completeHomog_two_apply_one_smul hΘ hv0 hv1, inv_smul_smul₀ hvn]

/-- **`Θ(h_2)(1)` in closed form**: the creation side of the `hlhs` clause at `[2]` and `(2,3)`,
written over the nine degree-six `e`-monomials.

`HJO.Mellit.theta_completeHomog_two_apply_one_smul` reduces it to
`qu(Q_{2,3}(Q_{2,3}1) - Q_{4,6}(1))`, and both vacuum values are known in exactly this basis:
`HJO.Sym.qop_two_three_apply_qop_two_three_apply_one` and `HJO.Sym.qop_four_six_apply_one`. So the
coefficients below are `qu` times their differences.

**Every one of the nine coefficients is nonzero**, and they carry `6, 2, 14, 16, 35, 6, 27, 19, 33`
terms in `(q,u)` — `158` in all, of total degree up to `11`. So there is nothing compact here, and
that is the finding: the creation side at `A = 2` is as dense as the sweep side.

Genericity: `M ≠ 0` for `HJO.Sym.Qop`'s `M^{-1}` in both vacuum values — so also `q ≠ 1` and `u ≠ 1`
— together with `qu ≠ 0` and `qu ≠ 1`. The scalar `1 + qu` is carried on the left and not inverted,
so this statement is true at `qu = -1` as well, where it says `0 = 0`. -/
theorem theta_completeHomog_two_apply_one (hM : (1 - q) * (1 - u) ≠ 0)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom 2 3 q u Θ) (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1) :
    (q * u + 1) • Θ (completeHomog L 2) 1
      =
        (q * u - q * u ^ 2 - q ^ 2 * u + q ^ 2 * u ^ 2 - q ^ 2 * u ^ 3 - q ^ 3 * u ^ 2)
            • (elemSymm L 1 ^ 3 * elemSymm L 3)
        + (-q * u - q ^ 2 * u ^ 2)
            • (elemSymm L 1 ^ 2 * elemSymm L 2 ^ 2)
        + (-q * u + q * u ^ 2 + q ^ 2 * u + q * u ^ 3 + q ^ 3 * u - q * u ^ 5 - q ^ 5 * u
            - q ^ 3 * u ^ 4 - q ^ 4 * u ^ 3 - q ^ 2 * u ^ 6 - q ^ 3 * u ^ 5 - q ^ 4 * u ^ 4
            - q ^ 5 * u ^ 3 - q ^ 6 * u ^ 2)
            • (elemSymm L 1 ^ 2 * elemSymm L 4)
        + (3 * q * u ^ 2 + 3 * q ^ 2 * u - 2 * q * u ^ 3 - 3 * q ^ 2 * u ^ 2 - 2 * q ^ 3 * u
            - q * u ^ 4 + 2 * q ^ 2 * u ^ 3 + 2 * q ^ 3 * u ^ 2 - q ^ 4 * u - 2 * q ^ 2 * u ^ 4
            - 3 * q ^ 3 * u ^ 3 - 2 * q ^ 4 * u ^ 2 - q ^ 2 * u ^ 5 - q ^ 3 * u ^ 4
            - q ^ 4 * u ^ 3 - q ^ 5 * u ^ 2)
            • (elemSymm L 1 * elemSymm L 2 * elemSymm L 3)
        + (q * u - 2 * q * u ^ 2 - 2 * q ^ 2 * u - q * u ^ 3 + q ^ 2 * u ^ 2 - q ^ 3 * u
            + 2 * q * u ^ 4 + 2 * q ^ 2 * u ^ 3 + 2 * q ^ 3 * u ^ 2 + 2 * q ^ 4 * u + q * u ^ 5
            - q ^ 2 * u ^ 4 - q ^ 3 * u ^ 3 - q ^ 4 * u ^ 2 + q ^ 5 * u + q ^ 2 * u ^ 5
            + 3 * q ^ 3 * u ^ 4 + 3 * q ^ 4 * u ^ 3 + q ^ 5 * u ^ 2 - q * u ^ 7 - q ^ 3 * u ^ 5
            - 2 * q ^ 4 * u ^ 4 - q ^ 5 * u ^ 3 - q ^ 7 * u - q ^ 3 * u ^ 6 - q ^ 4 * u ^ 5
            - q ^ 5 * u ^ 4 - q ^ 6 * u ^ 3 - q ^ 2 * u ^ 8 - q ^ 3 * u ^ 7 - q ^ 4 * u ^ 6
            - q ^ 5 * u ^ 5 - q ^ 6 * u ^ 4 - q ^ 7 * u ^ 3 - q ^ 8 * u ^ 2)
            • (elemSymm L 1 * elemSymm L 5)
        + (q * u - q * u ^ 2 - q ^ 2 * u + q ^ 2 * u ^ 2 - q ^ 2 * u ^ 3 - q ^ 3 * u ^ 2)
            • (elemSymm L 2 ^ 3)
        + (-q * u + 2 * q * u ^ 3 + q ^ 2 * u ^ 2 + 2 * q ^ 3 * u - q * u ^ 4 - q ^ 2 * u ^ 3
            - q ^ 3 * u ^ 2 - q ^ 4 * u + q * u ^ 5 + 2 * q ^ 2 * u ^ 4 + 2 * q ^ 3 * u ^ 3
            + 2 * q ^ 4 * u ^ 2 + q ^ 5 * u - q * u ^ 6 - 2 * q ^ 2 * u ^ 5 - 2 * q ^ 3 * u ^ 4
            - 2 * q ^ 4 * u ^ 3 - 2 * q ^ 5 * u ^ 2 - q ^ 6 * u + q ^ 2 * u ^ 6 + q ^ 6 * u ^ 2
            - q ^ 2 * u ^ 7 - q ^ 3 * u ^ 6 - q ^ 4 * u ^ 5 - q ^ 5 * u ^ 4 - q ^ 6 * u ^ 3
            - q ^ 7 * u ^ 2)
            • (elemSymm L 2 * elemSymm L 4)
        + (-q * u ^ 2 - q ^ 2 * u + q * u ^ 3 + 2 * q ^ 2 * u ^ 2 + q ^ 3 * u + q * u ^ 4
            - q ^ 2 * u ^ 3 - q ^ 3 * u ^ 2 + q ^ 4 * u - q * u ^ 5 + q ^ 3 * u ^ 3 - q ^ 5 * u
            + q ^ 2 * u ^ 5 + q ^ 5 * u ^ 2 - q ^ 2 * u ^ 6 - q ^ 3 * u ^ 5 - q ^ 4 * u ^ 4
            - q ^ 5 * u ^ 3 - q ^ 6 * u ^ 2)
            • (elemSymm L 3 ^ 2)
        + (q * u ^ 2 + q ^ 2 * u - q * u ^ 3 - 2 * q ^ 2 * u ^ 2 - q ^ 3 * u - q * u ^ 4
            - q ^ 4 * u + q ^ 2 * u ^ 4 + q ^ 3 * u ^ 3 + q ^ 4 * u ^ 2 + q * u ^ 6
            - q ^ 3 * u ^ 4 - q ^ 4 * u ^ 3 + q ^ 6 * u + q * u ^ 7 + 2 * q ^ 3 * u ^ 5
            + 3 * q ^ 4 * u ^ 4 + 2 * q ^ 5 * u ^ 3 + q ^ 7 * u - q * u ^ 8 - q ^ 4 * u ^ 5
            - q ^ 5 * u ^ 4 - q ^ 8 * u + q ^ 2 * u ^ 8 + q ^ 8 * u ^ 2 - q ^ 2 * u ^ 9
            - q ^ 3 * u ^ 8 - q ^ 4 * u ^ 7 - q ^ 5 * u ^ 6 - q ^ 6 * u ^ 5 - q ^ 7 * u ^ 4
            - q ^ 8 * u ^ 3 - q ^ 9 * u ^ 2)
            • (elemSymm L 6)
      := by
  rw [theta_completeHomog_two_apply_one_smul hΘ hv0 hv1,
    qop_two_three_apply_qop_two_three_apply_one hM, qop_four_six_apply_one hM]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_neg, map_mul, map_one,
    map_pow, map_ofNat]
  ring

end HJO.Mellit
