/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepWitnessLhsSingleton
public import HJO.Collinear.Commutation

/-! # The induction on the composition, and why the singleton case does not carry it

`HJO.Mellit.LhsComputes` (`HJO/Shuffle/SweepWitnessLhs.lean`) quantifies over every composition
`α` of every `N ≥ 1`. Apart from this file there is only the *extraction* at the singleton,
`HJO.Mellit.qop_apply_one_of_lhsComputes`, and no declaration in the other direction: no
induction on `α`, and no recursion on `ℓ`. This file supplies the induction, and measures what it
costs.

The answer is negative, and it is the point of the file.

## What is proved

* `HJO.Mellit.stageFromTotal_append`, `HJO.Mellit.stageWordTotal_append` — the stage word at the
  witness peels from the right, the mirror of `HJO.Mellit.stageWord_append` with no sweep system and
  no replication family. Unconditional.
* `HJO.Mellit.constantCoeff_lowerRun_stageWordTotal_append` — `lowerRun` peels its outermost `d_-`
  onto exactly the stage that `stageWordTotal_append` peels, so the whole `ℓ`-dependence of the
  clause's right-hand side is the single operator `d_-^{(ℓ+1)}G_{ℓ+1,A}` on `V_ℓ`.
* `HJO.Mellit.LhsWord` and `HJO.Mellit.lhsComputes_of_lhsWord` — the realisation quantifier of the
  clause discharged: the identity in `Λ` gives the clause for every realisation at once. Only one
  direction; the converse
  would need an injective realisation, which `HJO.Sym.IsRealisation` does not provide.
* `HJO.Mellit.lhsScalar_append` — the clause's scalar `(-1)^{(a-1)N}q^{ℓ-N}` appends by
  `(-1)^{(a-1)A}q^{1-A}` with **no hypothesis on `q` or `u`**: both exponents are nonpositive, so
  `HJO.Mellit.zpow_add_of_nonpos` applies. The same phenomenon as
  `HJO.Mellit.inductionScalar_append`, at `q` instead of `qu`.
* `HJO.Mellit.lhsWord_iff_lhsAppendStep` — **the induction, carried out, as an equivalence**: the
  clause is equivalent to its own append step. The base case (`HJO.Mellit.lhsAt_nil`) and all of the
  list and scalar bookkeeping cost nothing, so *all* of the content is in the step.
  `HJO.Mellit.lhsAt_append_iff` displays that step with everything peeled and the scalar factored.
* `HJO.Mellit.lhsAt_singleton_one_of_base` — the singleton clause, in the exact shape
  `HJO.Mellit.lhsBase_of_lhsSlope` delivers it, is one instance of the step: `β = ∅`, `A = 1`.

## The measurement: the singleton case does NOT suffice

One might hope to drive the step by the singleton clause, which is what
`HJO.Mellit.LhsSlope` supplies at every coprime slope. It cannot, and the obstruction is exact.

`HJO.Mellit.copComp_one_one_apply_one`: `C_1C_1(1) = q^{-1}e_1^2 + (1-q^{-1})e_2`. The second
creation operator is **not** multiplication by `e_1` — by `HJO.CreationSeeds.cop_elemSymm` it is
`e_1h_1 - (1-q^{-1})h_2`, and `h_2 = e_1^2 - e_2`.

`HJO.Sym.elemSymm_two_eq_axisGen`: `(v+1)e_2 = U_1^2 + vU_2` at `v = qu`. So `e_2` reads the
*second* axis generator, with coefficient `v`.

`HJO.Mellit.theta_copComp_one_one`, putting those together:
`(qu+1)·Θ(C_1C_1(1)) = (u+1)·Q_{a,b}^2 + u(q-1)·Q_{2a,2b}`.

And `HJO.Mellit.qop_double_apply_one_of_lhsWord`: since every scalar of the clause is `1` at
`α = (1,1)` (`N = ℓ = 2`), the clause there reads

`(u+1)·Q_{a,b}(Q_{a,b}1) + u(q-1)·Q_{2a,2b}(1) = (qu+1)·ct(d_-^2G_{2,1}G_{1,1}(1))`.

`Q_{2a,2b}` — the slope operator at the **doubled**, hence non-coprime, slope — occurs nowhere in
the clause at `α = (1)`, which by `HJO.Mellit.theta_copComp_one` mentions `Q_{a,b}` and nothing
else; and `u(q-1) ≠ 0` at every parameter where the clause is not vacuous, `q ≠ 1` being forced by
its own genericity `(1-q)(1-u) ≠ 0`. So the two-part composition already carries information the
singleton clause does not, at *any* slope: `LhsSlope` at `(a,b)` and at every other coprime
`(a',b')` is a statement about `Q_{a',b'}`, never about a collinear multiple.

Structurally: grading `k` of the sweep module corresponds to the collinear slope `(a(k+1), b(k+1))`,
and the step at grading `k` needs the collinear operator there. The singleton clause is the `k = 0`
instance. This is the same fact the remark at `HJO.Mellit.qop_apply_one_of_lhsComputes` records from
the other side, sharpened from "the bridge is needed for the base case" to "a bridge is needed at
every grading".

**Where the collinear operator comes from is *not* `HJO.Sweep.exists_slopeActions`**.
`HJO/Shuffle/MellitCollinearSplit.lean` settles it twice over:
`HJO.Sym.qop_collinear_eq_bracket` writes `Q_{ak,bk}` as `M^{-1}` times a commutator of slope
operators at two *coprime* slopes — `HJO.Sym.Qop`'s own non-coprime branch, with the split
identified as the primitive split of `(a,b)`, so independent of `k` — and
`HJO.Sweep.not_slopeActions_bridge` shows no map from the replicated action at the index `(ka,kb)`
computes `Q_{ka,kb}`, because `HJO.Sweep.exists_slopeActions` constrains its family only at coprime
indices. So the doubled slope is not an extra unknown; what the step needs is coprime slope
operators at first coordinate growing linearly in `α.sum`, applied to vectors other than the vacuum.

## A second structural finding: the two sides peel at opposite ends

`HJO.Sym.CopComp` is `C_{α_1}∘⋯∘C_{α_ℓ}`, so `α_ℓ` is the *innermost* creation operator and
appending a part changes the seed of the word rather than post-composing anything;
`HJO.Mellit.stage` puts `G_{ℓ,α_ℓ}` *outermost*. `HJO.Mellit.lhsAt_append_iff` displays this. The
consequence is that a step depending only on the value `ct(d_-^k(F))` — the only datum an induction
of the shape "carry the clause up the grading" has — cannot produce `CopComp q α`; it produces
`CopComp q α.reverse`. So an inductive step must carry the accumulated operator
`C_{α_1}⋯C_{α_{ℓ-1}}`, not just its value on the vacuum. That is a second reason the step is
non-local, independent of the slope obstruction above.

## This agrees with the intended proof

`HJO.Mellit.lhsRewrite_sweepWitness`'s own proof is **not** an induction on `α`. It is a flat chain:
`C_α` is put in closed form on the base action by `HJO.Mellit.map_constantCoeff_markedWordOp'`,
`C_α = (-1)^Nq^{ℓ-N}ρ^*_{0,1}(d_-^{\ell}y_1^{α_1-1}\cdots y_\ell^{α_\ell-1}d_+^{\ell})1`, the
conjugation monoid of the shift operators carries the base action to the `(a,b)`-replicated one, and
only then does `HJO.Mellit.mellitInduction_sweepWitness` identify the resulting word with the
composite of stages. The `α`-recursion lives in `HJO.Mellit.mellitInduction_sweepWitness`, on
the *braid* side, where the append lemma is `HJO.Mellit.braidRep_specialBraid_dplusIter` — a
statement about `π_k(B_{s,v,α})d_+^k(1)`, not about `Θ(C_α 1)`. So the route this file measures as
closed was never the route of that proof.

## Genericity

`HJO.Mellit.stageFromTotal_append`, `stageWordTotal_append`,
`constantCoeff_lowerRun_stageWordTotal_append`, `lhsScalar_append`, `lhsAt_nil`,
`lhsWord_iff_lhsAppendStep`, `lhsAt_append_iff` and `copComp_one_one_apply_one`: **none**, not even
`q ≠ 0`. `HJO.Sym.elemSymm_two_eq_axisGen`, `theta_copComp_one_one`,
`qop_double_apply_one_of_lhsWord` and `lhsAt_singleton_one_of_base`: `qu ≠ 0` and `qu ≠ 1`, which
are `HJO.Sym.axisGen_one`'s and `HJO.Mellit.theta_copComp_one`'s own. Evaluated at the degenerate
parameters: at `q = 1` the coefficient `u(q-1)` of the doubled-slope term is `0`, so the obstruction
disappears and this measurement is simply silent there.

**Note that `lhsComputes_iff_of_degenerate` does not show the clause is vacuous at `q = 1`.**
That declaration (`HJO/Shuffle/SweepWitnessLhsRefuted.lean`) is hypothesised on
`q * u = 0 ∨ q * u = 1`, and
`q = 1` gives `q * u = u`, which is neither in general. So it says nothing at `q = 1`, and whether
the clause is vacuous there is **not settled** by it or by anything else in this library. The
vanishing of the coefficient is arithmetic and stands.

At `u = 0` the coefficient also vanishes, and `qu = 0` is excluded. At
`qu = -1` the scalar `qu+1` on the left of `theta_copComp_one_one` is `0` and the statement says
nothing: that is the one coprime-slope parameter at which this measurement is silent, because `e_2`
is then not in the span of `U_1^2` and `U_2`.

## Implementation notes

This file shows that the route it measures to `HJO.Mellit.lhsRewrite_sweepWitness` is closed; that
theorem is proved by a different route (`HJO.Mellit.lhsRewrite_sweepWitness`,
`HJO/Shuffle/ShuffleClosed.lean`). `HJO.Sym.elemSymm_two_eq_axisGen` and
`HJO.Mellit.copComp_one_one_apply_one` are instances of `HJO.Sym.axisGen_one`'s and
`HJO.CreationSeeds.cop_elemSymm`'s families rather than results of their own.

`HJO.Collinear.Commutation` is imported only for `HJO.Sym.elemSymm_one_eq_X` (`e_1 = p_1` read
as the generator `X_0`), which the two degree-two Newton computations below need and which
`HJO.Shuffle.SweepWitnessLhsSingleton`'s chain does not reach.

## References

Declarations involved: `HJO.Mellit.lhsRewrite_sweepWitness`,
`HJO.Mellit.mellitInduction_sweepWitness`, `HJO.Mellit.braidRep_specialBraid_dplusIter`,
`HJO.Mellit.map_constantCoeff_markedWordOp'`, `HJO.CreationSeeds.cop_elemSymm`,
`HJO.CreationSeeds.copComp_cons`, `HJO.Sym.CopComp`, `HJO.Mellit.stage`, `HJO.Sym.axisGen`,
`HJO.Sym.IsSlopeHom`, `HJO.Sweep.exists_slopeActions`, `HJO.Sym.isSlopeHom_shiftsDegree`.
-/

@[expose] public section

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {a b : ℕ}

/-! ### Two values in degree two -/

/-- The scalar `1/2` of the two Newton recursions in degree two, as `(2 : L)⁻¹`. -/
theorem algebraMap_half (L : Type*) [Field L] [Algebra ℚ L] :
    algebraMap ℚ L (2⁻¹ : ℚ) = (2 : L)⁻¹ := by
  rw [map_inv₀, map_ofNat]

/-- `e_2 = (p_1² - p_2)/2`, from `HJO.Sym.elemSymm`'s Newton recursion. -/
theorem elemSymm_two_eq_X (L : Type*) [Field L] [Algebra ℚ L] :
    elemSymm L 2 = MvPolynomial.C ((2 : L)⁻¹) *
      ((MvPolynomial.X 0 : Lambda L) * MvPolynomial.X 0 - MvPolynomial.X 1) := by
  have h0 : elemSymm L 0 = 1 := by rw [elemSymm]
  have hp1 : powerSum L (0 + 1) = (MvPolynomial.X 0 : Lambda L) := rfl
  have hp2 : powerSum L (1 + 1) = (MvPolynomial.X 1 : Lambda L) := rfl
  rw [show (2 : ℕ) = 1 + 1 from rfl, elemSymm, Finset.sum_range_succ, Finset.sum_range_one,
    elemSymm_one_eq_X, h0, hp1, hp2, show (((1 : ℕ) : ℚ) + 1) = 2 from by norm_num,
    show ((2 : ℚ)⁻¹) = (2⁻¹ : ℚ) from rfl, algebraMap_half]
  ring

/-- `h_2 = (p_1² + p_2)/2`, from `HJO.Sym.completeHomog`'s Newton recursion. -/
theorem completeHomog_two_eq_X (L : Type*) [Field L] [Algebra ℚ L] :
    completeHomog L 2 = MvPolynomial.C ((2 : L)⁻¹) *
      ((MvPolynomial.X 0 : Lambda L) * MvPolynomial.X 0 + MvPolynomial.X 1) := by
  have h0 : completeHomog L 0 = 1 := by rw [completeHomog]
  have h1 : completeHomog L 1 = (MvPolynomial.X 0 : Lambda L) := by
    rw [HJO.CopPower.completeHomog_one]; rfl
  have hp1 : powerSum L (0 + 1) = (MvPolynomial.X 0 : Lambda L) := rfl
  have hp2 : powerSum L (1 + 1) = (MvPolynomial.X 1 : Lambda L) := rfl
  rw [show (2 : ℕ) = 1 + 1 from rfl, completeHomog, Finset.sum_range_succ, Finset.sum_range_one,
    h0, h1, hp1, hp2, show (((1 : ℕ) : ℚ) + 1) = 2 from by norm_num,
    show ((2 : ℚ)⁻¹) = (2⁻¹ : ℚ) from rfl, algebraMap_half]
  ring

/-- **`h_2 + e_2 = e_1²`.** The two Newton recursions in degree two differ only in the sign of
`p_2`, so their sum is `p_1²`. -/
theorem completeHomog_two_add_elemSymm_two (L : Type*) [Field L] [Algebra ℚ L] :
    completeHomog L 2 + elemSymm L 2 = elemSymm L 1 ^ 2 := by
  have h2 : (2 : L) ≠ 0 := by
    have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
    exact two_ne_zero
  have hhalf : (2 : L)⁻¹ + (2 : L)⁻¹ = 1 := by field_simp; norm_num
  rw [completeHomog_two_eq_X, elemSymm_two_eq_X, elemSymm_one_eq_X]
  rw [show (MvPolynomial.C ((2 : L)⁻¹) * ((MvPolynomial.X 0 : Lambda L) * MvPolynomial.X 0
      + MvPolynomial.X 1) + MvPolynomial.C ((2 : L)⁻¹) * ((MvPolynomial.X 0 : Lambda L) *
      MvPolynomial.X 0 - MvPolynomial.X 1))
    = MvPolynomial.C ((2 : L)⁻¹ + (2 : L)⁻¹) * ((MvPolynomial.X 0 : Lambda L) *
      MvPolynomial.X 0) from by rw [MvPolynomial.C_add]; ring]
  rw [hhalf, MvPolynomial.C_1, one_mul, sq]

/-! ### `e_2` on the axis generators -/

/-- **`(v+1)e_2 = U_1² + vU_2`**, the degree-two expansion on the axis generators of
`HJO.Sym.axisGen` at `v = qu`. The coefficient of `U_2` is `v`, nonzero whenever `v ≠ 0`, and the
scalar `v + 1` on the left is invertible off `v = -1`; so `e_2` genuinely reads `U_2`, and a slope
homomorphism's value on `e_2` genuinely reads the slope operator at the *doubled* slope.

The two hypotheses are `HJO.Sym.axisGen_one`'s: `v ≠ 0` for the substitution of
`HJO.Sym.plethAxis` and `v ≠ 1` for the normalising scalar `v/(v-1)` of `HJO.Sym.axisGen`. -/
theorem elemSymm_two_eq_axisGen {v : L} (hv0 : v ≠ 0) (hv1 : v ≠ 1) :
    MvPolynomial.C (v + 1) * elemSymm L 2
      = elemSymm L 1 ^ 2 + MvPolynomial.C v * axisGen v 2 := by
  have h2 : (2 : L) ≠ 0 := by
    have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
    exact two_ne_zero
  have hv : v - 1 ≠ 0 := sub_ne_zero_of_ne hv1
  obtain ⟨A, hA⟩ : ∃ A : L, A = v / (v - 1) * (2 : L)⁻¹ * ((v⁻¹ - 1) * (v⁻¹ - 1)) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : L, B = v / (v - 1) * (2 : L)⁻¹ * ((v ^ 2)⁻¹ - 1) := ⟨_, rfl⟩
  have hax : axisGen v 2
      = MvPolynomial.C A * ((MvPolynomial.X 0 : Lambda L) * MvPolynomial.X 0)
        + MvPolynomial.C B * MvPolynomial.X 1 := by
    rw [axisGen, completeHomog_two_eq_X, map_mul, map_add, map_mul, MvPolynomial.algHom_C,
      plethAxis_X, plethAxis_X, pow_one, show (1 : ℕ) + 1 = 2 from rfl, hA, hB]
    simp only [MvPolynomial.C_mul, MvPolynomial.algebraMap_eq]
    ring
  have hx : (v + 1) * (2 : L)⁻¹ = 1 + v * A := by rw [hA]; field_simp; ring
  have hy : -((v + 1) * (2 : L)⁻¹) = v * B := by rw [hB]; field_simp; ring
  have hlhs : MvPolynomial.C (v + 1) * elemSymm L 2
      = MvPolynomial.C (1 + v * A) * ((MvPolynomial.X 0 : Lambda L) * MvPolynomial.X 0)
        + MvPolynomial.C (v * B) * MvPolynomial.X 1 := by
    rw [elemSymm_two_eq_X, ← hy, ← hx, MvPolynomial.C_mul, MvPolynomial.C_neg,
      MvPolynomial.C_mul]
    ring
  rw [hlhs, hax, elemSymm_one_eq_X]
  simp only [MvPolynomial.C_add, MvPolynomial.C_mul, MvPolynomial.C_1]
  ring

end HJO.Sym

namespace HJO.Mellit

open HJO.Sym HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {a b : ℕ}

/-! ### The seed of the two-part composition `(1, 1)` -/

/-- **`C_1 C_1 (1) = q^{-1}e_1² + (1 - q^{-1})e_2`.** The first creation operator applied to
`C_1(1) = e_1` is *not* multiplication by `e_1`: by `HJO.CreationSeeds.cop_elemSymm` it is
`e_1h_1 - (1 - q^{-1})h_2`, and `h_2 = e_1² - e_2`
(`HJO.Sym.completeHomog_two_add_elemSymm_two`), so an `e_2` term survives with coefficient
`1 - q^{-1}`, which vanishes only at `q = 1`.

This is the computation that decides whether the singleton case of
`HJO.Mellit.lhsRewrite_sweepWitness` can carry an induction on the composition. See the module
docstring. -/
theorem copComp_one_one_apply_one (q : L) :
    CopComp q [1, 1] (1 : Lambda L)
      = MvPolynomial.C q⁻¹ * elemSymm L 1 ^ 2
        + MvPolynomial.C (1 - q⁻¹) * elemSymm L 2 := by
  have hcop : CopComp q [1, 1] = Cop q 1 * Cop q 1 := by rw [CopComp]; simp
  have hone : Cop q 1 (1 : Lambda L) = elemSymm L 1 := by
    have := copComp_one_apply_one (L := L) q
    rwa [show CopComp q [1] = Cop q 1 from by rw [CopComp]; simp] at this
  have hstep : Cop q 1 (elemSymm L 1)
      = elemSymm L 1 ^ 2 - MvPolynomial.C (1 - q⁻¹) * completeHomog L 2 := by
    rw [HJO.CreationSeeds.cop_elemSymm q 1 1]
    rw [show Finset.Icc 1 1 = {1} from rfl]
    simp only [Finset.sum_singleton, Nat.sub_self, elemSymm_zero, pow_one]
    rw [show ((1 : ℤ) - (1 : ℕ)) = 0 from by norm_num, zpow_zero, MvPolynomial.C_1, one_mul,
      show (1 : ℕ) + 1 = 2 from rfl, HJO.CopPower.completeHomog_one]
    rw [show (powerSum L 1 : Lambda L) = elemSymm L 1 from by rw [elemSymm_one]]
    ring
  have hC : (1 : Lambda L) - MvPolynomial.C (1 - q⁻¹) - MvPolynomial.C q⁻¹ = 0 := by
    rw [← MvPolynomial.C_1 (R := L) (σ := ℕ), ← MvPolynomial.C_sub, ← MvPolynomial.C_sub,
      show (1 : L) - (1 - q⁻¹) - q⁻¹ = 0 from by ring, MvPolynomial.C_0]
  rw [hcop, Module.End.mul_apply, hone, hstep,
    show completeHomog L 2 = elemSymm L 1 ^ 2 - elemSymm L 2 from by
      rw [← completeHomog_two_add_elemSymm_two L]; ring]
  linear_combination (elemSymm L 1 ^ 2) * hC


/-! ### The stage word peels from the right, at the witness -/

/-- **Appending a part post-composes one stage, at the witness.** The mirror of
`HJO.Mellit.stageFrom_append` for `HJO.Mellit.stageFromTotal`: no sweep system and no replication
family occurs. Unconditional. -/
theorem stageFromTotal_append (q u : L) (a b : ℕ) (α : List ℕ) (A : ℕ) :
    ∀ (k : ℕ) (F : Total L), stageFromTotal q u a b k F (α ++ [A])
      = stageTotal q u a b (k + α.length) A (stageFromTotal q u a b k F α) := by
  induction α with
  | nil => intro k F; rw [List.nil_append, stageFromTotal, stageFromTotal, stageFromTotal,
      List.length_nil, Nat.add_zero]
  | cons C β ih =>
    intro k F
    rw [List.cons_append, stageFromTotal, stageFromTotal, ih (k + 1) _, List.length_cons,
      show k + 1 + β.length = k + (β.length + 1) from by omega]

/-- **`G_{ℓ,α_ℓ} ⋯ G_{1,α_1}(1)` at `α ++ [A]`, at the witness.** The mirror of
`HJO.Mellit.stageWord_append`. Unconditional. -/
theorem stageWordTotal_append (q u : L) (a b : ℕ) (α : List ℕ) (A : ℕ) :
    stageWordTotal q u a b (α ++ [A])
      = stageTotal q u a b α.length A (stageWordTotal q u a b α) := by
  rw [stageWordTotal, stageWordTotal, stageFromTotal_append, Nat.zero_add]

/-- **Where an induction on the composition would have to bite.** The two recursions of the
right-hand side of `HJO.Mellit.LhsComputes` meet at the *top* index: `lowerRun` peels its outermost
`d_-`, which is the one immediately above the stage that `HJO.Mellit.stageWordTotal_append` peels.
So the whole `ℓ`-dependence of the clause's right-hand side is carried by the single operator
`d_-^{(ℓ+1)} G_{ℓ+1,A}` acting on `V_ℓ`, sandwiched inside `d_-^ℓ`.

An induction on the composition therefore reduces to one question: does
`ct ∘ d_-^ℓ ∘ (d_-^{(ℓ+1)}G_{ℓ+1,A})` factor through `ct ∘ d_-^ℓ`? The module docstring records why
the answer is no for `ℓ ≥ 1` even though it is yes for `ℓ = 0`. Unconditional. -/
theorem constantCoeff_lowerRun_stageWordTotal_append (q u : L) (a b : ℕ) (α : List ℕ) (A : ℕ) :
    MvPolynomial.constantCoeff (lowerRun q (α.length + 1) (stageWordTotal q u a b (α ++ [A])))
      = MvPolynomial.constantCoeff (lowerRun q α.length
          (dminus q (α.length + 1)
            (stageTotal q u a b α.length A (stageWordTotal q u a b α)))) := by
  rw [stageWordTotal_append, lowerRun, Module.End.mul_apply]

/-! ### The realisation quantifier, discharged -/

/-- **`HJO.Mellit.LhsComputes` with the realisation quantifier gone.** Both sides of the clause are
`ι` of an element of `Λ`, and `ι` is an algebra homomorphism, so the identity *in `Λ`* implies the
clause for every realisation at once.

Only one direction is available. The converse would need a realisation that is injective, and
`HJO.Sym.IsRealisation` does not assert one exists — so this is a genuine strengthening of the
clause, not a reformulation of it, and it is the shape everything below is stated at. -/
def LhsWord (q u : L) (a b : ℕ) : Prop :=
  ∀ Θ : Lambda L →ₐ[L] Module.End L (Lambda L), IsSlopeHom a b q u Θ →
    ∀ N : ℕ, 0 < N → ∀ α : List ℕ, (∀ x ∈ α, 0 < x) → α.sum = N →
      (-1 : L) ^ (N * (b + 1)) • Θ (CopComp q α 1) 1
        = ((-1 : L) ^ ((a - 1) * N) * q ^ ((α.length : ℤ) - (N : ℤ))) •
            MvPolynomial.constantCoeff (lowerRun q α.length (stageWordTotal q u a b α))

/-- **The `Λ`-level identity implies the clause.** -/
theorem lhsComputes_of_lhsWord (h : LhsWord q u a b) : LhsComputes q u a b := by
  intro ι _ Θ hΘ N hN α hpos hsum
  rw [← map_smul ι, ← map_smul ι, h Θ hΘ N hN α hpos hsum]

/-! ### What the clause says at `α = (1, 1)`

Every scalar of `HJO.Mellit.LhsComputes` is `1` at `α = (1,1)`: `N = ℓ = 2`, so `q^{ℓ-N} = q^0`,
`(-1)^{(a-1)N}` and `(-1)^{N(b+1)}` are both even powers. So the clause there is the bare identity
`Θ(C_1C_1(1))1 = ct(d_-^2 G_{2,1}G_{1,1}(1))`, and the theorems below evaluate its left-hand
side. -/

/-- **`Θ(C_1C_1 1)` reads the slope operator at the DOUBLED slope.** For every slope homomorphism
at `(a,b)`,

`(qu+1)·Θ(C_1C_1(1)) = (u+1)·Q_{a,b}² + u(q-1)·Q_{2a,2b}`.

This is the obstruction to any induction on the composition whose only input is the clause at
`α = (1)`. The singleton clause pins `Θ` on `C_1(1) = e_1 = -U_1` and so mentions `Q_{a,b}` and
nothing else (`HJO.Mellit.theta_copComp_one`); but the two-part composition `(1,1)` already
mentions `Q_{2a,2b}`, with coefficient `u(q-1)`, which is nonzero at every parameter the clause is
not vacuous at. The reason is `HJO.Mellit.copComp_one_one_apply_one`: the second creation operator
is **not** multiplication by `e_1`, and the discrepancy `(1-q^{-1})e_2` reads `U_2`
(`HJO.Sym.elemSymm_two_eq_axisGen`).

Genericity used: `qu ≠ 0` (hence `q ≠ 0`) and `qu ≠ 1`, which are `HJO.Sym.axisGen_one`'s and
`HJO.Mellit.theta_copComp_one`'s own hypotheses. -/
theorem copComp_one_one_apply_one_axisGen (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1) :
    MvPolynomial.C (q * u + 1) * CopComp q [1, 1] (1 : Lambda L)
      = MvPolynomial.C (u + 1) * elemSymm L 1 ^ 2
        + MvPolynomial.C (u * (q - 1)) * axisGen (q * u) 2 := by
  have hq0 : q ≠ 0 := fun h => hv0 (by rw [h, zero_mul])
  have h1 := copComp_one_one_apply_one (L := L) q
  have h2 := elemSymm_two_eq_axisGen (L := L) hv0 hv1
  have hs1 : (MvPolynomial.C (u + 1) : Lambda L)
      = MvPolynomial.C (q * u + 1) * MvPolynomial.C q⁻¹ + MvPolynomial.C (1 - q⁻¹) := by
    rw [← MvPolynomial.C_mul, ← MvPolynomial.C_add]
    congr 1
    field_simp
    ring
  have hs2 : (MvPolynomial.C (u * (q - 1)) : Lambda L)
      = MvPolynomial.C (1 - q⁻¹) * MvPolynomial.C (q * u) := by
    rw [← MvPolynomial.C_mul]
    congr 1
    field_simp
  rw [hs1, hs2]
  linear_combination MvPolynomial.C (q * u + 1) * h1 + MvPolynomial.C (1 - q⁻¹) * h2

/-- **`Θ(C_1C_1 1)` reads the slope operator at the DOUBLED slope.** For every slope homomorphism
at `(a,b)`,

`(qu+1)·Θ(C_1C_1(1)) = (u+1)·Q_{a,b}² + u(q-1)·Q_{2a,2b}`.

This is the obstruction to any induction on the composition whose only input is the clause at
`α = (1)`. The singleton clause pins `Θ` on `C_1(1) = e_1 = -U_1` and so mentions `Q_{a,b}` and
nothing else (`HJO.Mellit.theta_copComp_one`); the two-part composition `(1,1)` already mentions
`Q_{2a,2b}`, with coefficient `u(q-1)`. The reason is
`HJO.Mellit.copComp_one_one_apply_one`: the second creation operator is **not** multiplication by
`e_1`, and the discrepancy `(1-q^{-1})e_2` reads `U_2` (`HJO.Sym.elemSymm_two_eq_axisGen`).

Genericity used: `qu ≠ 0` (hence `q ≠ 0`, which the `q^{-1}` of `HJO.Sym.Cop`'s displacement needs)
and `qu ≠ 1`; these are `HJO.Sym.axisGen_one`'s hypotheses and `HJO.Mellit.theta_copComp_one`'s. -/
theorem theta_copComp_one_one (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom a b q u Θ) :
    (q * u + 1) • Θ (CopComp q [1, 1] (1 : Lambda L))
      = (u + 1) • (Qop q u a b * Qop q u a b)
        + (u * (q - 1)) • Qop q u (a * 2) (b * 2) := by
  have he1 : Θ (elemSymm L 1) = -Qop q u a b := by
    rw [← neg_neg (elemSymm L 1), ← axisGen_one hv0 hv1, map_neg, hΘ 1 Nat.one_pos, mul_one,
      mul_one]
  have h := congrArg Θ (copComp_one_one_apply_one_axisGen (L := L) hv0 hv1)
  rw [← MvPolynomial.smul_eq_C_mul, ← MvPolynomial.smul_eq_C_mul, ← MvPolynomial.smul_eq_C_mul,
    map_smul, map_add, map_smul, map_smul, map_pow, he1, hΘ 2 (by omega), neg_sq,
    pow_two] at h
  exact h

/-- **The clause at `α = (1,1)` determines the doubled-slope operator on the vacuum.** Reading
`HJO.Mellit.LhsWord` at `α = (1,1)`, where every scalar is `1`, and substituting
`HJO.Mellit.theta_copComp_one_one`:

`(u+1)·Q_{a,b}(Q_{a,b}1) + u(q-1)·Q_{2a,2b}(1) = (qu+1)·ct(d_-^2 G_{2,1}G_{1,1}(1))`.

So the clause at the *two-part* composition is an identity **about `Q_{2a,2b}`**, an operator that
does not occur in the clause at `α = (1)` at all. Since `u(q-1) ≠ 0` whenever `u ≠ 0` and `q ≠ 1`
— and `q ≠ 1` is forced by the clause's own genericity, `(1-q)(1-u) ≠ 0` — the doubled-slope term
cannot be discarded. This is the precise sense in which
`HJO.Mellit.qop_apply_one_of_lhsComputes`'s remark is right: the clause is not reducible to its
singleton case, and an induction on the composition needs the bridge at *every* collinear slope,
not only at `(a,b)`. -/
theorem qop_double_apply_one_of_lhsWord (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom a b q u Θ)
    (h : LhsWord q u a b) :
    (u + 1) • Qop q u a b (Qop q u a b (1 : Lambda L))
        + (u * (q - 1)) • Qop q u (a * 2) (b * 2) (1 : Lambda L)
      = (q * u + 1) •
          MvPolynomial.constantCoeff (lowerRun q 2 (stageWordTotal q u a b [1, 1])) := by
  have key := h Θ hΘ 2 (by omega) [1, 1] (by simp) (by simp)
  simp only [List.length_cons, List.length_nil] at key
  rw [show ((-1 : L) ^ (2 * (b + 1))) = 1 from by rw [pow_mul]; norm_num,
    show ((-1 : L) ^ ((a - 1) * 2)) = 1 from by rw [mul_comm, pow_mul]; norm_num,
    show (((0 + 1 + 1 : ℕ) : ℤ) - ((2 : ℕ) : ℤ)) = 0 from by norm_num, zpow_zero, mul_one,
    one_smul, one_smul] at key
  have hstage : (0 + 1 + 1 : ℕ) = 2 := by norm_num
  rw [hstage] at key
  have hop := theta_copComp_one_one hv0 hv1 hΘ
  have := congrArg (fun T : Module.End L (Lambda L) => T (1 : Lambda L)) hop
  simp only [LinearMap.smul_apply, LinearMap.add_apply, Module.End.mul_apply] at this
  rw [key] at this
  exact this.symm


/-! ### The induction on the composition, exactly

`HJO.Mellit.LhsAt` is the clause at one composition, and `HJO.Mellit.LhsAppendStep` is the step of
the induction that peels its last part. The point of `HJO.Mellit.lhsWord_iff_lhsAppendStep` is that
the two are *equivalent*: the induction itself — the base case at `α = ∅`, the recursion of
`HJO.Mellit.stageWordTotal_append`, and all of the scalar bookkeeping — costs nothing, and the whole
content of the clause sits in the step. -/

/-- **The clause of `HJO.Mellit.lhsRewrite_sweepWitness` at one composition, at the `Λ` level**, for
a fixed slope homomorphism and with no positivity or `N ≥ 1` hypothesis, so that the empty
composition is in range. -/
def LhsAt (q u : L) (a b : ℕ) (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) (α : List ℕ) : Prop :=
  (-1 : L) ^ (α.sum * (b + 1)) • Θ (CopComp q α 1) 1
    = ((-1 : L) ^ ((a - 1) * α.sum) * q ^ ((α.length : ℤ) - (α.sum : ℤ))) •
        MvPolynomial.constantCoeff (lowerRun q α.length (stageWordTotal q u a b α))

/-- **The base case is `1 = 1`.** At the empty composition `C_∅ = 1`, `Θ(1) = 1`, `d_-^0 = 1` and
the stage word is the unit, and every scalar is `1`. Unconditional — in particular this is the
corner `HJO.Mellit.LhsComputes` excludes with `0 < N` and which costs nothing. -/
theorem lhsAt_nil (q u : L) (a b : ℕ) (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) :
    LhsAt q u a b Θ [] := by
  rw [LhsAt, show CopComp q ([] : List ℕ) = 1 from by rw [CopComp]; simp]
  simp only [List.sum_nil, List.length_nil, Nat.mul_zero, pow_zero, Nat.cast_zero, sub_zero,
    zpow_zero, mul_one, one_smul, Module.End.one_apply, map_one, Nat.zero_mul, pow_zero]
  rw [stageWordTotal, stageFromTotal, lowerRun, Module.End.one_apply, map_one]

omit [Algebra ℚ L] in
/-- **The clause's scalars append with no hypothesis on `q` or `u`.** The sign multiplies by
`(-1)^{(a-1)A}` and the power of `q` by `q^{1-A}`, and `1 - A ≤ 0` because a part is positive, so
`HJO.Mellit.zpow_add_of_nonpos` applies and `q = 0` is not excluded. This is the same phenomenon as
`HJO.Mellit.inductionScalar_append`, at `q` instead of `qu`. -/
theorem lhsScalar_append (q : L) (a : ℕ) {α : List ℕ} {A : ℕ} (hα : ∀ x ∈ α, 0 < x)
    (hA : 0 < A) :
    ((-1 : L) ^ ((a - 1) * (α ++ [A]).sum) *
        q ^ (((α ++ [A]).length : ℤ) - ((α ++ [A]).sum : ℤ)))
      = ((-1 : L) ^ ((a - 1) * A) * q ^ (1 - (A : ℤ))) *
          ((-1 : L) ^ ((a - 1) * α.sum) * q ^ ((α.length : ℤ) - (α.sum : ℤ))) := by
  have hlen : α.length ≤ α.sum := length_le_sum_of_forall_pos hα
  have hs : (α ++ [A]).sum = α.sum + A := by
    simp only [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
  have hl : (α ++ [A]).length = α.length + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
  have hsign : (-1 : L) ^ ((a - 1) * (α.sum + A))
      = (-1 : L) ^ ((a - 1) * A) * (-1 : L) ^ ((a - 1) * α.sum) := by
    rw [← pow_add]; congr 1; ring
  have hexp : ((α.length + 1 : ℕ) : ℤ) - ((α.sum + A : ℕ) : ℤ)
      = (1 - (A : ℤ)) + (((α.length : ℕ) : ℤ) - ((α.sum : ℕ) : ℤ)) := by push_cast; ring
  rw [hs, hl, hsign, hexp, zpow_add_of_nonpos q (by omega) (by omega)]
  ring

/-- **The step of the induction on the composition**: the clause at `β` carries to the clause at
`β ++ [A]`, for every positive part `A`. -/
def LhsAppendStep (q u : L) (a b : ℕ) : Prop :=
  ∀ Θ : Lambda L →ₐ[L] Module.End L (Lambda L), IsSlopeHom a b q u Θ →
    ∀ β : List ℕ, (∀ x ∈ β, 0 < x) → ∀ A : ℕ, 0 < A →
      LhsAt q u a b Θ β → LhsAt q u a b Θ (β ++ [A])

/-- **The induction, carried out.** From the step, the clause holds at every composition with
positive parts — the base case being `HJO.Mellit.lhsAt_nil`, which is free. -/
theorem lhsAt_of_lhsAppendStep (h : LhsAppendStep q u a b)
    (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) (hΘ : IsSlopeHom a b q u Θ) :
    ∀ α : List ℕ, (∀ x ∈ α, 0 < x) → LhsAt q u a b Θ α := by
  intro α
  induction α using List.reverseRecOn with
  | nil => intro _; exact lhsAt_nil q u a b Θ
  | append_singleton β A ih =>
    intro hpos
    have hβ : ∀ x ∈ β, 0 < x := fun x hx => hpos x (List.mem_append_left _ hx)
    have hA : 0 < A := hpos A (List.mem_append_right _ (List.mem_singleton_self A))
    exact h Θ hΘ β hβ A hA (ih hβ)

/-- **`HJO.Mellit.LhsWord` is exactly its append step.** Read left to right this says the step is
forced; read right to left it is the induction. So the induction on the composition costs nothing
and *all* of the clause is in the step — which is what
`HJO.Mellit.qop_double_apply_one_of_lhsWord` then measures. -/
theorem lhsWord_iff_lhsAppendStep : LhsWord q u a b ↔ LhsAppendStep q u a b := by
  constructor
  · intro h Θ hΘ β hβ A hA _
    have hA' : 0 < (β ++ [A]).sum := by
      have : (β ++ [A]).sum = β.sum + A := by
        simp only [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
      omega
    exact h Θ hΘ _ hA' (β ++ [A])
      (fun x hx => by
        rcases List.mem_append.1 hx with hx | hx
        · exact hβ x hx
        · rw [List.mem_singleton.1 hx]; exact hA) rfl
  · intro h Θ hΘ N _ α hpos hsum
    subst hsum
    exact lhsAt_of_lhsAppendStep h Θ hΘ α hpos

/-! ### The singleton clause is the step at the empty composition, and only that -/

/-- **The base case, in the shape `HJO.Mellit.lhsBase_of_lhsSlope` delivers it, is
`HJO.Mellit.LhsAt` at `α = (1)`.** So the singleton clause at `(a,b)` — the whole output of the
general-slope gluing identity `HJO.Mellit.LhsSlope` — is exactly one instance of the step: the one
with `β = ∅` and `A = 1`.

The hypothesis is verbatim the conclusion of `HJO.Mellit.lhsBase_of_lhsSlope`, so this composes with
that theorem without importing it. -/
theorem lhsAt_singleton_one_of_base (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom a b q u Θ)
    (hbase : (-1 : L) ^ b • Qop q u a b (1 : Lambda L)
      = (-1 : L) ^ (a - 1) •
          MvPolynomial.constantCoeff (lowerRun q 1 (stageWordTotal q u a b [1]))) :
    LhsAt q u a b Θ [1] := by
  rw [LhsAt, theta_copComp_one hv0 hv1 hΘ]
  simp only [List.sum_cons, List.sum_nil, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.add_zero, one_mul, Nat.cast_one, sub_self, zpow_zero, mul_one]
  rw [LinearMap.neg_apply, smul_neg, ← neg_smul,
    show -((-1 : L) ^ (b + 1)) = (-1) ^ b from by rw [pow_succ]; ring]
  exact hbase


/-- **The append step, with everything peeled and the scalars factored out.** Both sides of the
clause at `β ++ [A]` split: the creation side because `HJO.Sym.CopComp` is a product of operators,
so appending a part changes the *seed* of the word from `1` to `C_A(1)`; the sweep side because
`HJO.Mellit.stageWordTotal_append` puts one further stage on the outside and
`HJO.Mellit.lowerRun`'s own recursion immediately lowers it. And the clause's scalar factors as
`HJO.Mellit.lhsScalar_append` says, with no hypothesis on `q` or `u`.

Reading this off is what shows the two sides peel at *opposite ends*: `α_ℓ` is the innermost
creation operator and the outermost stage. Every scalar and every list index of the induction is
discharged here, so what an inductive step has to supply is exactly this identity — and the
theorems above measure that it is strictly more than the singleton clause. -/
theorem lhsAt_append_iff {β : List ℕ} {A : ℕ} (hβ : ∀ x ∈ β, 0 < x) (hA : 0 < A)
    (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) :
    LhsAt q u a b Θ (β ++ [A]) ↔
      (-1 : L) ^ ((β.sum + A) * (b + 1)) • Θ (CopComp q β (Cop q A 1)) 1
        = ((-1 : L) ^ ((a - 1) * A) * q ^ (1 - (A : ℤ)) *
            ((-1 : L) ^ ((a - 1) * β.sum) * q ^ ((β.length : ℤ) - (β.sum : ℤ)))) •
          MvPolynomial.constantCoeff (lowerRun q β.length
            (dminus q (β.length + 1)
              (stageTotal q u a b β.length A (stageWordTotal q u a b β)))) := by
  have hs : (β ++ [A]).sum = β.sum + A := by
    simp only [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
  have hl : (β ++ [A]).length = β.length + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
  have hcop : CopComp q (β ++ [A]) (1 : Lambda L) = CopComp q β (Cop q A 1) := by
    rw [CopComp, CopComp, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      Module.End.mul_apply]
  rw [LhsAt, hcop, lhsScalar_append q a hβ hA, hs, hl,
    constantCoeff_lowerRun_stageWordTotal_append]

end HJO.Mellit
