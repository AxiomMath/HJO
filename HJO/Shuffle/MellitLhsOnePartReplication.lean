/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitLhsCompNoInduction
public import HJO.Shuffle.MellitLhsSlopeBase
public import HJO.Shuffle.SweepAppendWidth
public import HJO.Shuffle.MellitAppend
public import HJO.Shuffle.MellitTwoPartTwoThree

/-! # The one-part compositions of `HJO.Mellit.lhsRewrite_sweepWitness`: the sweep side replicates,
the creation side does not

On the *other* leg of the shuffle assumption, `HJO.Mellit.mellitInduction_sweepWitness`, the
instance at `(a,b) = (2,3)`, `N = 2`, `α = (2)` was reduced through **one replicated letter**:
`HJO.Sweep.stageTotal_two_eq` says `G_{k+1,2} = Z^{(k+1)}_{a,b}G_{k+1,1}`, so the stage word at
`α = (2)` is one known operator applied to the known `N = 1` seed. This file asks whether
`HJO.Mellit.LhsWord` admits the same reduction at a one-part composition `α = [A]`, and separates
the two halves of the answer.

## The sweep side replicates, at every part and every slope

`HJO.Mellit.stageWordTotal_singleton_eq_replicated_pow` is the general statement the `A = 2` case
was an instance of:

`G_{1,A}(1) = (Z^{(1)}_{a,b})^{A-1} (G_{1,1}(1))`

for every `A`, every `(a,b)` and no hypothesis at all. So on the sweep side the whole `A`-dependence
of the clause at a one-part composition is `A - 1` copies of one operator on one seed — the stage
word, the replication family and the separating level are gone, exactly as on the other leg, and at
every `A` rather than only at `A = 2`.

Two things make this *stronger* here than there. First,
`HJO.Mellit.stageWordTotal_singleton_mem_piece` : the whole family lives in `V_1`, because the
replicated letter preserves the grading (`HJO.Mellit.replicatedTotal_pow_mem_piece`). At the grading
`0` the two conjugating trains of `HJO.Mellit.replicatedLetter` are empty
(`HJO.Mellit.replicatedTotal_zero`), so the operator being iterated is `Ω(2;a,b)` itself, whose
factors are `HJO.Sweep.slopeOperator` at the grading `1` and `HJO.Sweep.zopOneStar` at the grading
`1` — and the latter reads `d_-` and `d^*_+` at the indices `1` and `2` and no higher. So evaluating
the sweep side at *every* one-part composition is a width-`≤ 2` computation. Second, at
`(a,b) = (2,3)` the seed is computed outright:
`HJO.Mellit.stageWordTotal_two_three_singleton` puts it as
`(Z^{(1)}_{2,3})^{A-1}(-e_1y_1^2 + uy_1^3)`, by `HJO.Sweep.stageTotal_two_three_zero_one_one`.

`HJO.Mellit.lhsAt_two_three_singleton_iff` collects this: the clause at `(2,3)`, `α = [A]` is
*equivalent* to one identity whose sweep half is `ct(d_-((Z^{(1)}_{2,3})^{A-1}(-e_1y_1^2+uy_1^3)))`.

## The creation side does not, and that is the whole obstruction

What the reduction does **not** do is give the clause at `[A]` from the clause at `[1]`, and the
step that fails is on the creation side, not the sweep side. The clause at `[A]` reads
`Θ(C_A(1)) = (-q)^{1-A}Θ(h_A)` (`HJO.Mellit.copComp_singleton_apply_one`), and
`HJO.Mellit.copComp_singleton_not_mem_adjoin_axisGen`
(`HJO/Shuffle/MellitLhsCompNoInduction.lean`) already proves that this seed is **not** a
polynomial in the axis generators of index `< A`. Since `HJO.Sym.IsSlopeHom` is the only information
a slope homomorphism carries, the clause at `[A]` reads `Q_{Aa,Ab}` — an operator the clause at
`[1]`, which pins `Θ` on `C_1(1) = e_1 = -U_1` and nothing else (`HJO.Mellit.theta_copComp_one`),
never mentions. So no reduction of the clause at `[A]` to the clause at `[1]` exists, replicated
letter or not.

This is a *different* failure from the one the three append data suffer. There
(`HJO.Mellit.lhsWord_iff_lhsVecAppendStep`, `HJO.Mellit.lhsWord_iff_lhsOpAppendStep`) the step's
hypothesis is already a theorem, so the datum transports nothing and the step is empty. Here the
sweep-side hypothesis is genuine and is genuinely used — `HJO.Mellit.stageTotal_apply` is doing
work, the stage word really is eliminated — and the reduction still fails, because it never touches
the side of the clause where the new slope operator appears. The residual at a one-part composition
is therefore exactly `Θ(h_A)(1)`, and nothing on the sweep side.

## Genericity

`HJO.Mellit.stageWordTotal_singleton_eq_replicated_pow`,
`HJO.Mellit.stageWordTotal_singleton_mem_piece` and
`HJO.Mellit.lhsAt_singleton_iff_replicated`: **none**. The equivalence is a rewriting of both sides
of the clause and holds at every parameter, including the degenerate ones — which is why it settles
nothing by itself.

`HJO.Mellit.stageWordTotal_two_three_singleton` and `HJO.Mellit.lhsAt_two_three_singleton_iff`:
`q ≠ 0`, `u ≠ 0`, `q ≠ 1`, which are `HJO.Sweep.stageTotal_two_three_zero_one_one`'s own. Each is
the inverse-becomes-zero hazard and not bookkeeping: at `q = 0` or `u = 0` the letter `(qu)^{-1}z_1`
of `HJO.Sweep.slopeOperator` inside the replicated letter is the zero map, and at `q = 1` the
scalar `q^k/(1-q)` of `HJO.Sweep.zop` is undefined, so the clause would be false there rather than
vacuous.

## References

This file bears on `HJO.Mellit.lhsRewrite_sweepWitness`, using `HJO.Mellit.stage`,
`HJO.Mellit.replicatedLetter`, `HJO.Sweep.slopeOperator`, `HJO.Sweep.zop`, `HJO.Sym.Cop`,
`HJO.Sym.CopComp`, `HJO.Sym.IsSlopeHom` and `HJO.Sweep.dminus`.
-/

@[expose] public section

namespace HJO.Mellit

open HJO.Sym HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {a b : ℕ}

/-! ### `d_-^1` is one lowering operator -/

/-- **`d_-^1 = d_-^{(1)}`.** The `ℓ = 1` case of `HJO.Mellit.lowerRun`, which a one-part composition
is read at. -/
theorem lowerRun_one (q : L) : lowerRun q 1 = dminus q 1 := by
  rw [lowerRun, lowerRun, one_mul]

/-! ### The stage word at a one-part composition is a power of the replicated letter -/

/-- **`G_{1,A}(1) = (Z^{(1)}_{a,b})^{A-1}(G_{1,1}(1))`.** The stage word at a one-part composition
is `A - 1` copies of the replicated letter of `HJO.Mellit.replicatedLetter` on the stage word at
`A = 1`. This is the general form of `HJO.Sweep.stageTotal_two_eq`, which is the case `A = 2`: the
power `A - 1` of `HJO.Mellit.stage` is the *only* place the part `A` enters the stage, so the
`A`-dependence of the right-hand side of `HJO.Mellit.lhsRewrite_sweepWitness` at a one-part
composition is a single operator iterated.

Unconditional, at every `(a,b)`, every `A` — including `A = 0`, where both sides are the `A = 1`
stage word, the truncated subtraction of `HJO.Mellit.stage` making `G_{1,0} = G_{1,1}`. -/
theorem stageWordTotal_singleton_eq_replicated_pow (q u : L) (a b A : ℕ) :
    stageWordTotal q u a b [A]
      = (replicatedTotal q u a b 0 ^ (A - 1)) (stageWordTotal q u a b [1]) := by
  rw [stageWordTotal_singleton, stageWordTotal_singleton, stageTotal_apply, stageTotal_apply,
    Nat.sub_self, pow_zero, Module.End.one_apply]

/-- **The whole one-part family lives in `V_1`.** `HJO.Mellit.replicatedLetter` preserves the
grading (`HJO.Mellit.replicatedTotal_pow_mem_piece`) and the stage raises it by exactly one
(`HJO.Mellit.stageTotal_mem_piece`), so no one-part composition reaches a width the `N = 1` case did
not.

This is what makes the one-part family a *computation* rather than a structural question: the
operator being iterated is `Ω(2;a,b)` at the grading `0` (`HJO.Mellit.replicatedTotal_zero`), whose
factors read `d_-` and `d^*_+` at the indices `1` and `2` and no higher. Unconditional. -/
theorem stageWordTotal_singleton_mem_piece (q u : L) (a b A : ℕ) :
    stageWordTotal q u a b [A] ∈ piece L 1 := by
  rw [stageWordTotal_singleton]
  exact stageTotal_mem_piece q u a b 0 A (Subalgebra.one_mem _)

/-! ### The clause at a one-part composition, with the stage word gone -/

/-- **`HJO.Mellit.LhsAt` at a one-part composition, reduced through the replicated letter.**

Both sides are rewritten and nothing is assumed: the creation side by
`HJO.Mellit.copComp_singleton_apply_one`, which makes the seed `(-q)^{1-A}h_A`, and the sweep side
by `HJO.Mellit.stageWordTotal_singleton_eq_replicated_pow`, which removes the stage word in favour
of `A - 1` copies of one explicit operator on one explicit vector. The `ℓ = 1` run of lowering
operators is the single `d_-^{(1)}` of `HJO.Mellit.lowerRun_one`.

This is the mirror, on `hlhs`, of `HJO.Mellit.mellitInduction_two_three_two_iff_dsc`, and it holds
at every part `A` rather than only at `A = 2`. What it shows is that the residual at a one-part
composition is entirely `Θ(h_A)(1)`: see
`HJO.Mellit.copComp_singleton_not_mem_adjoin_axisGen` for why that residual is *not* reachable from
the clause at `[1]`.

Unconditional — in particular this is a reformulation of the clause and not a weakening of it. -/
theorem lhsAt_singleton_iff_replicated (q u : L) (a b A : ℕ)
    (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) :
    LhsAt q u a b Θ [A] ↔
      ((-1 : L) ^ (A * (b + 1)) * (-q) ^ (1 - (A : ℤ))) • Θ (completeHomog L A) 1
        = ((-1 : L) ^ ((a - 1) * A) * q ^ (1 - (A : ℤ))) •
            MvPolynomial.constantCoeff (dminus q 1
              ((replicatedTotal q u a b 0 ^ (A - 1)) (stageWordTotal q u a b [1]))) := by
  rw [LhsAt, copComp_singleton_apply_one, stageWordTotal_singleton_eq_replicated_pow,
    ← MvPolynomial.smul_eq_C_mul, map_smul]
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.cast_one, LinearMap.smul_apply, smul_smul, lowerRun_one]

/-! ### At `(a,b) = (2,3)`: one explicit operator on one explicit seed -/

/-- **The one-part stage word at `(a,b) = (2,3)`, at every part.**
`HJO.Sweep.stageTotal_two_three_zero_one_one` evaluates the `A = 1` seed as `-e_1y_1^2 + uy_1^3`,
so the stage word at `α = [A]` is `A - 1` copies of the replicated letter on that polynomial, with
every sweep operator of the `N = 1` case discharged and none of a higher width introduced.

This generalises `HJO.Sweep.stageWordTotal_two_three_two` from `A = 2` to every `A`.

Genericity: `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, all three
`HJO.Sweep.stageTotal_two_three_zero_one_one`'s own. -/
theorem stageWordTotal_two_three_singleton (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) (A : ℕ) :
    stageWordTotal q u 2 3 [A]
      = (replicatedTotal q u 2 3 0 ^ (A - 1))
          (-(MvPolynomial.C (elemSymm L 1) * (auxVar 1 : Total L) ^ 2)
            + u • (auxVar 1 : Total L) ^ 3) := by
  rw [stageWordTotal_singleton_eq_replicated_pow, stageWordTotal_singleton,
    stageTotal_two_three_zero_one_one hq0 hu0 hq1]

/-- **The clause at `(a,b) = (2,3)` and a one-part composition, with everything explicit on the
sweep side.** The sweep half is one explicit polynomial, one explicit operator and a power; the
creation half is `Θ(h_A)(1)`.

At `A = 1` the sweep half is `Q_{2,3}(1)` outright
(`HJO.Sweep.dminus_one_stageTotal_two_three_zero_one_one`), which is the decided singleton case; at
`A ≥ 2` it is a width-`≤ 2` evaluation of `A - 1` copies of `Ω(2;2,3)`
(`HJO.Mellit.stageWordTotal_singleton_mem_piece`), and the creation half reads `Q_{2A,3A}`
(`HJO.Mellit.copComp_singleton_not_mem_adjoin_axisGen`). So the one-part family of `hlhs` owes a
computation on one side and a new slope operator on the other, and the replicated letter reaches
only the first.

Genericity: `q ≠ 0`, `u ≠ 0`, `q ≠ 1`. -/
theorem lhsAt_two_three_singleton_iff (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) (A : ℕ)
    (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) :
    LhsAt q u 2 3 Θ [A] ↔
      Θ (completeHomog L A) 1
        = -MvPolynomial.constantCoeff (dminus q 1
            ((replicatedTotal q u 2 3 0 ^ (A - 1))
              (-(MvPolynomial.C (elemSymm L 1) * (auxVar 1 : Total L) ^ 2)
                + u • (auxVar 1 : Total L) ^ 3))) := by
  have hne : ((-1 : L) ^ A * q ^ (1 - (A : ℤ))) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (zpow_ne_zero _ hq0)
  have hm1 : ((-1 : L) ^ (1 - (A : ℤ))) = -((-1 : L) ^ A) := by
    rw [zpow_sub₀ (neg_ne_zero.2 (one_ne_zero (α := L))), zpow_one, zpow_natCast]
    rcases Nat.even_or_odd A with h | h
    · rw [h.neg_one_pow]; norm_num
    · rw [h.neg_one_pow]; norm_num
  have hs1 : ((-1 : L) ^ (A * (3 + 1)) * (-q) ^ (1 - (A : ℤ)))
      = -((-1 : L) ^ A * q ^ (1 - (A : ℤ))) := by
    rw [show A * (3 + 1) = 2 * (2 * A) from by ring, pow_mul,
      show ((-1 : L) ^ 2) = 1 from by norm_num, one_pow, one_mul,
      show (-q : L) = (-1) * q from by ring, mul_zpow, hm1]
    ring
  have hs2 : ((-1 : L) ^ ((2 - 1) * A) * q ^ (1 - (A : ℤ)))
      = ((-1 : L) ^ A * q ^ (1 - (A : ℤ))) := by
    rw [show (2 - 1) * A = A from by omega]
  rw [lhsAt_singleton_iff_replicated, stageWordTotal_two_three_singleton hq0 hu0 hq1, hs1, hs2,
    neg_smul, neg_eq_iff_eq_neg, ← smul_neg]
  exact (smul_right_injective _ hne).eq_iff

/-! ### The consistency check: at `A = 1` the reduced form IS the decided singleton clause -/

/-- **`HJO.Mellit.lhsAt_two_three_singleton_iff` at `A = 1` reproves the singleton clause.**

The scalars of `HJO.Mellit.lhsAt_singleton_iff_replicated` were normalised away in
`HJO.Mellit.lhsAt_two_three_singleton_iff`, and a sign lost there would make the equivalence state a
different theorem while still being an equivalence. This is the check that no sign was lost: at
`A = 1` the power of the replicated letter is empty, the seed's lowering is
`HJO.Sweep.dminus_one_stageTotal_two_three_zero_one_one`'s `Q_{2,3}(1)`, the creation side is
`h_1 = e_1 = -U_1` (`HJO.Mellit.theta_copComp_one`), and the two sides match on the nose.

The conclusion is not new — it also follows from
`HJO.Mellit.lhsAt_singleton_one_of_base`, `HJO.Mellit.lhsBase_of_lhsSlope` and
`HJO.Mellit.lhsSlope_two_odd` at `(2, 2k+1)`. It is stated here only as a check on the reduced
form.

Genericity spent: `q ≠ 0`, `u ≠ 0`, `q ≠ 1` for the seed; `(1-q)(1-u) ≠ 0` — so also `u ≠ 1` — for
`HJO.Sym.Qop`'s `M^{-1}` in `HJO.Sweep.dminus_one_stageTotal_two_three_zero_one_one`; and `qu ≠ 0`,
`qu ≠ 1` for `HJO.Sym.axisGen_one`. -/
theorem lhsAt_two_three_one_of_singleton_iff (hM : (1 - q) * (1 - u) ≠ 0) (hq0 : q ≠ 0)
    (hu0 : u ≠ 0) (hq1 : q ≠ 1) (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom 2 3 q u Θ) :
    LhsAt q u 2 3 Θ [1] := by
  have hh1 : completeHomog L 1 = elemSymm L 1 := by
    rw [HJO.CopPower.completeHomog_one, elemSymm_one]
  have hthe : Θ (elemSymm L 1) = -Qop q u 2 3 := by
    rw [← copComp_one_apply_one q]
    exact theta_copComp_one hv0 hv1 hΘ
  rw [lhsAt_two_three_singleton_iff hq0 hu0 hq1, Nat.sub_self, pow_zero, Module.End.one_apply,
    ← stageTotal_two_three_zero_one_one (L := L) hq0 hu0 hq1,
    dminus_one_stageTotal_two_three_zero_one_one hM hq0 hu0 hq1, MvPolynomial.constantCoeff_C,
    hh1, hthe]
  simp

end HJO.Mellit
