/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitZopOneV1
public import HJO.Shuffle.SweepInductionInstanceTwo
public import HJO.Shuffle.SweepReplicatedWidthTwo

/-! # The one-part family at `(2,3)`, in a form that iterates

`HJO.Mellit.lhsAt_two_three_singleton_iff` reduces the `hlhs` clause at a one-part composition
`[A]` and `(a,b) = (2,3)` to
`Θ(h_A)(1) = -ct(d_-^{(1)}((Z^{(1)}_{2,3})^{A-1}(-e_1y_1^2 + uy_1^3)))`, and
`HJO.Sweep.replicatedTotal_two_three_zero_eq_width_two` shows the operator being iterated reads no
index above `2`. What was still missing was the *evaluation*: a form of the right-hand side in which
every step is a named operator on `Λ` rather than a composite of substitutions on the total space.

This file supplies the two ends of that computation and the recursion between them.

## The three pieces

* **The last step.** `HJO.Sweep.constantCoeff_dminus_one_of_mem_piece`: on `V_1` the composite
  `ct ∘ d_-^{(1)}` is the Hall--Littlewood sum `∑_m B_m(G_m)` over the `y_1`-expansion
  `G = ∑_m G_my_1^m` — `HJO.Sym.Bop` at the index `m` on the `m`-th coefficient, and nothing else.
  So the projection at the end of the clause is one operator of `HJO.Sym.Bop` per monomial.

* **The step.** `HJO.Sweep.zopOneStar_one_of_mem_piece` (in `HJO/Shuffle/MellitZopOneV1.lean`)
  already evaluates `z_1` on the whole of `V_1` in terms of `HJO.Sym.Bop`, `HJO.Sweep.bopExt` and
  `d^*_+{}^{(0)}`; with `HJO.Sweep.replicatedTotal_two_three_zero_apply` the replicated letter is
  two of those around a multiplication by `y_1^2`, and
  `HJO.Sweep.auxVar_sq_mul_zopOneStar_one_mem_piece` is the closure fact that lets the second one be
  applied to the output of the first. `HJO.Sweep.replicatedTotal_two_three_zero_of_mem_piece` is the
  step with the *outer* `z_1` expanded.

* **The recursion.** `HJO.Mellit.stageWordTotal_singleton_succ`: the one-part stage word at `[A+2]`
  is one replicated letter on the one-part stage word at `[A+1]`, at every `(a,b)` and with no
  hypothesis. So the family `A ↦ G_A := G_{1,A}(1)` is generated from
  `G_1 = -e_1y_1^2 + uy_1^3` by one operator, and stays inside `V_1`
  (`HJO.Mellit.stageWordTotal_singleton_mem_piece`).

`HJO.Mellit.lhsAt_two_three_singleton_iff_bop` assembles the three: the clause at `[A]` says exactly

`Θ(h_A)(1) = -∑_m B_m((G_A)_m)`,

with `G_A` the recursion's value. Both halves are now statements about `Λ` and the named operators
`HJO.Sym.Bop`, `HJO.Sweep.bopExt`, `d^*_+{}^{(0)}` — no sweep word, no train, no braid
representation, no replication family, and no operator of width above `2`.

## What this does and does not settle

It does **not** decide the clause. What it gives is a decision *procedure* for each fixed `A`: run
the recursion `A - 1` times and compare. Outside Lean, that procedure has been run: at `A = 1` the
answer is `e_1e_2 + (q + u - 1)e_3` — which is `-Q_{2,3}(1)`, the decided singleton case
(`HJO.Sweep.dminus_one_stageTotal_two_three_zero_one_one`, `HJO.Sym.qop_two_three_apply_one`) — and
it is *not* compact for `A ≥ 2`: the answer is homogeneous of degree `3A`, and its expansion in the
`e`-monomials has `2`, `9` and `26` terms at `A = 1, 2, 3`, of `q`-degree `1`, `8` and `21`. So
there is no short closed form in `A` to be had at this level, and the residual on the creation side
remains `Θ(h_A)(1)`, which
`HJO.Mellit.copComp_singleton_not_mem_adjoin_axisGen` shows is not reachable from the clause at
`[1]`.

## Genericity

`HJO.Sweep.constantCoeff_dminus_one_of_mem_piece`,
`HJO.Sweep.auxVar_sq_mul_zopOneStar_one_mem_piece`,
`HJO.Sweep.replicatedTotal_two_three_zero_of_mem_piece` and
`HJO.Mellit.stageWordTotal_singleton_succ`: **none**. Every scalar is carried symbolically, so at
`q = 1` the `z_1` identities read `0 = 0` and at `q = 0` or `u = 0` they are unconditional
identities of two polynomial expressions.

`HJO.Mellit.lhsAt_two_three_singleton_iff_bop`: `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, all three inherited from
`HJO.Mellit.lhsAt_two_three_singleton_iff` and each the inverse-becomes-zero hazard: in a field
`0⁻¹ = 0`, so at `q = 0` or `u = 0` the letter `(qu)^{-1}z_1` of `HJO.Sweep.slopeOperator` is the
zero map and at `q = 1` the scalar `q/(1-q)` of `HJO.Sweep.zop` collapses, and there the clause is
false rather than vacuous.

## References

This file concerns `HJO.Mellit.lhsRewrite_sweepWitness`, using `HJO.Mellit.stage`,
`HJO.Mellit.replicatedLetter`, `HJO.Sweep.zop`, `HJO.Sweep.dminus`, `HJO.Sym.Bop`,
`HJO.Sweep.dplusStar`, `HJO.Sym.completeHomog` and `HJO.Sym.elemSymm`.
-/

@[expose] public section

namespace HJO.Sweep

open HJO.Sym HJO.Mellit

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The last step of the clause: `ct ∘ d_-^{(1)}` on `V_1` -/

/-- **`ct(d_-^{(1)}G) = ∑_m B_m(G_m)` for `G = ∑_m G_my_1^m ∈ V_1`.** The lowering operator on a
monomial of `V_1` is one Hall--Littlewood operator of `HJO.Sym.Bop`
(`HJO.Sweep.dminus_one_auxVar_pow_mul_C`), whose value is a constant of the total space, so the
constant-term map only strips the `MvPolynomial.C`. The sum is over `G.support`, which for an
element of `V_1` is a set of powers of `y_1` alone
(`HJO.Sweep.exists_single_zero_of_mem_piece_one`), and `d 0` is that power.

`G ∈ V_1` is not decoration: on a monomial carrying `y_2` the index `d 0` is not the whole exponent
and `HJO.Sweep.dminus_one_auxVar_pow_mul_C` does not apply.

No hypothesis on `q` or `u`. -/
theorem constantCoeff_dminus_one_of_mem_piece (q : L) {G : Total L} (hG : G ∈ piece L 1) :
    MvPolynomial.constantCoeff (dminus q 1 G)
      = ∑ d ∈ G.support, Bop q ((d 0 : ℕ) : ℤ) (MvPolynomial.coeff d G) := by
  conv_lhs => rw [G.as_sum]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨m, rfl⟩ := exists_single_zero_of_mem_piece_one hG hd
  have hmon : (auxVar 1 : Total L) ^ m * MvPolynomial.C (MvPolynomial.coeff
      (Finsupp.single 0 m) G) = MvPolynomial.monomial (Finsupp.single 0 m)
        (MvPolynomial.coeff (Finsupp.single 0 m) G) := by
    rw [auxVar, Nat.sub_self, MvPolynomial.X_pow_eq_monomial, mul_comm,
      MvPolynomial.C_mul_monomial, mul_one]
  rw [Finsupp.single_eq_same, ← hmon, dminus_one_auxVar_pow_mul_C, MvPolynomial.constantCoeff_C]

/-! ### The step stays inside `V_1` -/

/-- **`y_1^2z_1(F) ∈ V_1` for `F ∈ V_1`.** `z_1` preserves the grading
(`HJO.Sweep.zopOneStar_mem_piece`) and `y_1 ∈ V_1`, a subalgebra. This is the closure fact that
lets the evaluation `HJO.Sweep.zopOneStar_one_of_mem_piece` be applied a second time, to the
output of the first. -/
theorem auxVar_sq_mul_zopOneStar_one_mem_piece (q u : L) {F : Total L} (hF : F ∈ piece L 1) :
    (auxVar 1 : Total L) ^ 2 * zopOneStar q u 1 F ∈ piece L 1 :=
  mul_mem (pow_mem (auxVar_mem_piece le_rfl le_rfl) 2) (zopOneStar_mem_piece q u le_rfl hF)

/-! ### One step of the replicated letter, at the `Λ` level -/

/-- **The replicated letter at `(2,3)` on `V_1`, with the outer `z_1` evaluated.** The word is
`(qu)^{-1}y_1z_1y_1^2z_1` (`HJO.Sweep.replicatedTotal_two_three_zero_apply`); the outer `z_1` meets
`y_1^2z_1(F)`, which is in `V_1` by
`HJO.Sweep.auxVar_sq_mul_zopOneStar_one_mem_piece`, so
`HJO.Sweep.zopOneStar_one_of_mem_piece` evaluates it as a sum over the monomials of that element:
`HJO.Sym.Bop` applied to the coefficient before the displacement `d^*_+{}^{(0)}`, minus
`HJO.Sweep.bopExt` applied after it.

Applying the same lemma to the inner `z_1` — legitimate by `hF` — turns the whole step into
`Λ`-level data. No hypothesis on `q` or `u`. -/
theorem replicatedTotal_two_three_zero_of_mem_piece (q u : L) {F : Total L}
    (hF : F ∈ piece L 1) :
    replicatedTotal q u 2 3 0 F
      = ((q * u)⁻¹ * (q / (1 - q))) • ((auxVar 1 : Total L) *
          ∑ d ∈ ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 1 F).support,
            (dplusStar q u 0 (MvPolynomial.C (Bop q ((d 0 : ℕ) : ℤ) (MvPolynomial.coeff d
                ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 1 F))))
              - bopExt q ((d 0 : ℕ) : ℤ) (dplusStar q u 0 (MvPolynomial.C
                  (MvPolynomial.coeff d
                    ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 1 F)) : Total L)))) := by
  rw [replicatedTotal_two_three_zero_apply,
    zopOneStar_one_of_mem_piece q u (auxVar_sq_mul_zopOneStar_one_mem_piece q u hF),
    mul_smul_comm, smul_smul]

end HJO.Sweep

namespace HJO.Mellit

open HJO.Sym HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The recursion in the part -/

/-- **`G_{1,A+2}(1) = Z^{(1)}_{a,b}(G_{1,A+1}(1))`.** One step of
`HJO.Mellit.stageWordTotal_singleton_eq_replicated_pow`: the one-part stage word at `[A+2]` is one
replicated letter of `HJO.Mellit.replicatedLetter` on the one-part stage word at `[A+1]`.

The offset is necessary and not cosmetic: the power in `HJO.Mellit.stage` is `A - 1` with the
truncated subtraction, so `G_{1,0} = G_{1,1}` and the step from `[0]` to `[1]` applies no letter at
all.

Unconditional, at every `(a,b)` and every `A`. -/
theorem stageWordTotal_singleton_succ (q u : L) (a b A : ℕ) :
    stageWordTotal q u a b [A + 2]
      = replicatedTotal q u a b 0 (stageWordTotal q u a b [A + 1]) := by
  rw [stageWordTotal_singleton_eq_replicated_pow, stageWordTotal_singleton_eq_replicated_pow,
    show A + 2 - 1 = (A + 1 - 1) + 1 from by omega, pow_succ']
  rfl

/-! ### The clause at a one-part composition, entirely at the `Λ` level -/

/-- **`HJO.Mellit.LhsAt` at `(a,b) = (2,3)` and `[A]`: `Θ(h_A)(1) = -∑_m B_m((G_A)_m)`.**

The sweep side of the clause is now a finite sum of Hall--Littlewood operators of `HJO.Sym.Bop`,
one per monomial of the one-part stage word, and nothing else:
`HJO.Sweep.constantCoeff_dminus_one_of_mem_piece` evaluates `ct ∘ d_-^{(1)}` on `V_1`, and
`HJO.Mellit.stageWordTotal_singleton_mem_piece` is the membership it spends.

Together with `HJO.Mellit.stageWordTotal_singleton_succ` — which generates `G_A` from
`G_1 = -e_1y_1^2 + uy_1^3` (`HJO.Mellit.stageWordTotal_two_three_singleton`) by one operator whose
factors are `d^*_+` at the indices `0` and `1` and `d_-` at the indices `1` and `2`
(`HJO.Sweep.replicatedTotal_two_three_zero_eq_width_two`), and whose action on `V_1` is
`HJO.Sweep.replicatedTotal_two_three_zero_of_mem_piece` — this is a decision procedure for the
clause at each fixed `A`.

Genericity: `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, all three
`HJO.Mellit.lhsAt_two_three_singleton_iff`'s own. -/
theorem lhsAt_two_three_singleton_iff_bop (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) (A : ℕ)
    (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) :
    LhsAt q u 2 3 Θ [A] ↔
      Θ (completeHomog L A) 1
        = -∑ d ∈ (stageWordTotal q u 2 3 [A]).support,
            Bop q ((d 0 : ℕ) : ℤ)
              (MvPolynomial.coeff d (stageWordTotal q u 2 3 [A] : Total L)) := by
  rw [lhsAt_two_three_singleton_iff hq0 hu0 hq1,
    ← stageWordTotal_two_three_singleton hq0 hu0 hq1,
    constantCoeff_dminus_one_of_mem_piece q (stageWordTotal_singleton_mem_piece q u 2 3 A)]

/-! ### The two consistency checks on the reduced form -/

/-- **`A = 1`: the Hall--Littlewood sum is `Q_{2,3}(1) = -e_1e_2 + (1-q-u)e_3`.**

The sweep side of `HJO.Mellit.lhsAt_two_three_singleton_iff_bop` at `A = 1` is
`HJO.Sweep.dminus_one_stageTotal_two_three_zero_one_one`'s value, re-read through the
Hall--Littlewood sum: the seed `-e_1y_1^2 + uy_1^3` has two monomials, so the sum has the two terms
`B_2(-e_1)` and `B_3(u)`, and their total is `Q_{2,3}(1)`
(`HJO.Sym.qop_two_three_apply_one`). A sign lost in the reduction would show up here.

Genericity spent: `q ≠ 0`, `u ≠ 0`, `q ≠ 1` for the seed and `(1-q)(1-u) ≠ 0` — so also `u ≠ 1` —
for `HJO.Sym.Qop`'s `M^{-1}`, all four
`HJO.Sweep.dminus_one_stageTotal_two_three_zero_one_one`'s own. -/
theorem sum_bop_stageWordTotal_two_three_one (hM : (1 - q) * (1 - u) ≠ 0) (hq0 : q ≠ 0)
    (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    ∑ d ∈ (stageWordTotal q u 2 3 [1] : Total L).support,
        Bop q ((d 0 : ℕ) : ℤ) (MvPolynomial.coeff d (stageWordTotal q u 2 3 [1] : Total L))
      = -(elemSymm L 1 * elemSymm L 2) + (1 - q - u) • elemSymm L 3 := by
  rw [← constantCoeff_dminus_one_of_mem_piece q (stageWordTotal_singleton_mem_piece q u 2 3 1),
    stageWordTotal_singleton, dminus_one_stageTotal_two_three_zero_one_one hM hq0 hu0 hq1,
    MvPolynomial.constantCoeff_C, qop_two_three_apply_one hM]

/-- **The `A = 1` instance of `HJO.Mellit.lhsAt_two_three_singleton_iff_bop` is the decided
singleton clause**: the reduced form pins `Θ(h_1)(1) = e_1e_2 - (1-q-u)e_3`, i.e. `-Q_{2,3}(1)`.

This is the check on the normalisation: the equivalence would still be an equivalence with a sign
lost in it, and here it is checked against the already-decided clause at `[1]`
(`HJO.Mellit.lhsAt_two_three_one_of_singleton_iff`). -/
theorem theta_completeHomog_one_of_slopeHom (hM : (1 - q) * (1 - u) ≠ 0) (hq0 : q ≠ 0)
    (hu0 : u ≠ 0) (hq1 : q ≠ 1) (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom 2 3 q u Θ) :
    Θ (completeHomog L 1) 1 = elemSymm L 1 * elemSymm L 2 - (1 - q - u) • elemSymm L 3 := by
  have h := (lhsAt_two_three_singleton_iff_bop hq0 hu0 hq1 1 Θ).1
    (lhsAt_two_three_one_of_singleton_iff hM hq0 hu0 hq1 hv0 hv1 hΘ)
  rw [h, sum_bop_stageWordTotal_two_three_one hM hq0 hu0 hq1]
  abel

/-- **`A = 2`: the seed of the recursion is minus the `N = 1` invariant.**

`HJO.Sweep.stageWordTotal_two_three_two_eq_replicated_neg_dsc` pins the one-part stage word at `[2]`
independently, as one replicated letter on `-D_{5/2,c_{(1)}}` (`HJO.Mellit.dsc_two_three_one`,
which evaluates to `e_1y_1^2 - uy_1^3`). This says that vector *is* the stage word at `[1]`, so
that statement is exactly the `A = 0` case of `HJO.Mellit.stageWordTotal_singleton_succ`: the
recursion agrees with the independently decided `A = 2` reduction.

Genericity: `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, the seed's own. -/
theorem stageWordTotal_two_three_one_eq_neg_dsc (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    stageWordTotal q u 2 3 [1]
      = -(dsc q u 2 3 1 (sepLevel 2 1) (compColouring 2 3 [1]) : Total L) := by
  rw [stageWordTotal_singleton, stageTotal_two_three_zero_one_one hq0 hu0 hq1,
    dsc_two_three_one q u hq0 hq1, ← scal_mul_eq_smul_total,
    show (auxVar 1 : Total L) = MvPolynomial.X 0 from rfl]
  ring

end HJO.Mellit
