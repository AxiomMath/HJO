/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepWitnessLhs
public import HJO.Symmetric.AxisFree
public import HJO.Collinear.HAlphabet
public import HJO.CreationSeeds.Basic

/-! # What `HJO.Mellit.LhsComputes` costs at its smallest instance, and what pins `Θ`

`HJO.Mellit.LhsComputes` is what the `LhsRewrite` clause of `HJO.Mellit.MellitInput` costs at
`HJO.Mellit.sweepWitness` (`HJO.Mellit.lhsRewrite_sweepWitness_iff_lhsComputes`). Its left side is
`ι (Θ (C_α 1) 1)` for an *arbitrary* slope homomorphism `Θ` and realisation `ι`, so before anything
can be computed one has to know what `HJO.Sym.IsSlopeHom` actually determines. This file answers
that, and then reads the clause at `α = (1)`, where every quantifier is discharged and the residue
is a single identity.

## What `IsSlopeHom` gives, and where it gives nothing

`HJO.Sym.IsSlopeHom a b q u Θ` is one prescription: `Θ (U_k) = Q_{ak,bk}` for `k ≥ 1`, on the axis
generators `HJO.Sym.axisGen (q u) k` and nowhere else. Two regimes:

* at `v = qu` nonzero and not a root of unity the axis generators freely generate
  (`HJO.Sym.axisSub_bijective`), and then `Θ` is **unique**:
  `HJO.Sym.isSlopeHom_unique`;
* at `v = 0` and at `v = 1` every axis generator is the zero element
  (`HJO.Sym.axisGen_eq_zero`: the scalar `v/(v - 1)` of `HJO.Sym.axisGen` vanishes at both), so
  `IsSlopeHom a b q u Θ` becomes a condition **not mentioning `Θ`** at all —
  `HJO.Sym.isSlopeHom_iff_of_degenerate`. There `Θ` is not pinned even slightly, and
  `HJO.Mellit.lhsComputes_rhs_eq_zero_of_degenerate` shows what that does to the clause: the
  constant-term homomorphism `HJO.Sym.constHom` is then a slope homomorphism, its value on the
  creation seed is `0` because the seed is homogeneous of positive degree, and the clause collapses
  to the assertion that its own right-hand side vanishes.

`HJO.Mellit.LhsComputes` carries no hypothesis on `q` or `u`, so the second regime is inside its
statement. It is harmless for the equivalence — `LhsRewrite` quantifies over `Θ` the same way, so
the two Props degenerate together and nothing is weakened — but it means any proof of
`LhsComputes` must either exclude `v ∈ {0, 1}` by hand or refute
`∀ k ≥ 1, Q_{ak,bk} = 0` there.

**The second alternative is not one.**
`HJO/Shuffle/SweepWitnessLhsRefuted.lean` shows the clause is FALSE in this regime wherever a
slope homomorphism exists there at all, hence at `(q, u) = (1,1)`, `(0,1)` and `(1,0)` for every
`1 < a` (`HJO.Mellit.not_lhsComputes_of_degenerate`), and
`HJO.Mellit.lhsComputes_iff_of_degenerate` shows it is true at `v ∈ {0,1}` exactly when it is
vacuous. So refuting `∀ k ≥ 1, Q_{ak,bk} = 0` would empty the clause rather than rescue it: only
exclusion by hypothesis remains. The mechanism is `HJO.Sym.Qop`'s `((1-q)(1-u))⁻¹`, which is the
zero map at `q = 1` and at `u = 1` — the defect class of `HJO.Mellit.not_sweepAppend_one_left`.

## The smallest instance, and what it asks for

At `α = (1)` the seed is `C_1(1) = h_1 = e_1 = -U_1` (`HJO.Mellit.copComp_one_apply_one` with
`HJO.Sym.axisGen_one`), so `Θ` is pinned on it outright, by the `k = 1` case of the prescription
and nothing else: `HJO.Mellit.theta_copComp_one` gives `Θ (C_{(1)} 1) = -Q_{a,b}`. The clause then
reads, with no `Θ` and no `ι`-independent content left,

`(-1)^b • ι(Q_{a,b} 1) = (-1)^{a-1} • ι(constantCoeff(lowerRun q 1 (stageWordTotal (1))))`

-- `HJO.Mellit.qop_apply_one_of_lhsComputes`. The left-hand side is the slope operator of
`HJO.Sym.Qop`, an iterated commutator of the basic operators `D_n` inside `Module.End L (Lambda L)`;
the right-hand side is a word in the sweep operators of `HJO.Sweep.piece` inside
`HJO.Sweep.Total L`, written out by `HJO.Mellit.stageWordTotal_singleton_one`. No statement of the
library relates the two at `Q_{a,b}`: the only fact about `HJO.Sym.Qop` outside the symmetric
functions is its degree shift (`HJO.Sym.qop_shiftsDegree`). One statement does relate the two
one step lower down: for the basic operator `D_1`,
`HJO.Sweep.dop_one_eq_neg_dminusCM_dplusStar` (`HJO/CarlssonMellit/DopFromDplusStar.lean`) gives
`C(D_1 f) = -d_-(d^*_+(C f))`, with no hypothesis on `q` or `u`. Since `Q_{1,n} = D_n`
(`HJO.Sym.qop_one`), that is the base case of the bridge at `n = 1`, and the general `D_n` is what
is missing.

That is the negative result this file records. `MellitInduction` reduces to
`HJO.Mellit.SweepAppend` without the braid layer because both of its sides are words in the *same*
operators; `LhsComputes` is a bridge between two different algebras, and even its `N = 1` instance
is one, so no induction on `α` can avoid the bridge. The bridge is `HJO.Sweep.exists_slopeActions`
together with `HJO.Mellit.map_constantCoeff_markedWordOp'`; the sign discrepancy between the two
normalisations is `HJO.Dyck.Tilde.rel_biHomogeneous`.

All three of those are proved, and the bridge is still not available: neither
`HJO.Sweep.exists_slopeActions` (`HJO/Shuffle/SlopeActions.lean`) nor
`HJO.Mellit.map_constantCoeff_markedWordOp'`
(`HJO/CarlssonMellit/LoweringSumClosed.lean`) mentions `HJO.Sym.Qop` or `HJO.Sym.Dop` in
its statement — the first produces actions into `Module.End L (HJO.Sweep.Vstar L)`, the second
reads a marked word against a path character series. The statement carrying `Θ(C_α 1)` out of
`Module.End L (Lambda L)` is unnamed, and it is what remains.

## The sign bookkeeping

`HJO.Mellit.neg_one_pow_bigrading` verifies the arithmetic over `ℕ` with truncated
subtraction: `(-1)^{N(b+1)}` times the bigrading discrepancy `(-1)^{N(a+b)}` is `(-1)^{(a-1)N}`,
**provided `0 < a`**. At `a = 0` the truncation makes `(a-1)N = 0` while `N(a+1) = N`, so the two
differ at odd `N`; `HJO.Mellit.neg_one_pow_bigrading_ne_of_a_eq_zero` records that. Nothing
downstream reads `a = 0` (`lhsRewrite_sweepWitness_iff_lhsComputes` carries `0 < a`), so the
exponent as written in `LhsComputes` is sound where it is used.

## Implementation notes

`HJO.Sym.isSlopeHom_unique` is the uniqueness half of the statement whose existence half is
`HJO.Sym.exists_isSlopeHom`, and the rest are facts about this library's own definitions.
-/

@[expose] public section

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {a b : ℕ}

/-! ### What the prescription on the axis generators determines -/

/-- **The axis generators degenerate to zero at `v = 0` and at `v = 1`.** `HJO.Sym.axisGen` carries
the scalar `v / (v - 1)`, which is `0` at `v = 0` and — division by zero being `0` in a field — also
at `v = 1`. So at those two parameters `U_k = 0` for every `k`, and the prescription
`Θ(U_k) = Q_{ak,bk}` says nothing about `Θ`. -/
theorem axisGen_eq_zero {v : L} (h : v = 0 ∨ v = 1) (k : ℕ) : axisGen v k = 0 := by
  rw [axisGen, show v / (v - 1) = 0 from by rcases h with h | h <;> simp [h]]
  simp

/-- **At a degenerate parameter `IsSlopeHom` is a condition on `q, u, a, b` alone.** Both sides of
the prescription are then forced: the left is `Θ 0 = 0` by `HJO.Sym.axisGen_eq_zero`, so what
remains is the vanishing of the slope operators. In particular every algebra homomorphism satisfies
`IsSlopeHom` as soon as one does, and `Θ` is not determined at all. -/
theorem isSlopeHom_iff_of_degenerate (h : q * u = 0 ∨ q * u = 1)
    (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) :
    IsSlopeHom a b q u Θ ↔ ∀ k : ℕ, 0 < k → Qop q u (a * k) (b * k) = 0 := by
  rw [IsSlopeHom]
  refine forall_congr' fun k => forall_congr' fun _ => ?_
  rw [axisGen_eq_zero h, map_zero, eq_comm]

/-- **Away from the degenerate parameters a slope homomorphism is unique.** The composite
`Θ ∘ axisSub v` is pinned on every generator `p_{i+1}` by the prescription, so two slope
homomorphisms agree after `axisSub v`, and `HJO.Sym.axisSub_surjective`,
which is where `v ≠ 0` and `v` not a root of unity are spent — removes it.

This is the uniqueness half of what `HJO.Sym.exists_isSlopeHom` gives the
existence half of, under exactly the same hypotheses on `v = qu`. -/
theorem isSlopeHom_unique [CharZero L] (hv0 : q * u ≠ 0) (hv1 : ∀ j : ℕ, (q * u) ^ (j + 1) ≠ 1)
    {Θ Θ' : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom a b q u Θ) (hΘ' : IsSlopeHom a b q u Θ') : Θ = Θ' := by
  have key : Θ.comp (axisSub (q * u)) = Θ'.comp (axisSub (q * u)) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_comp, Function.comp_apply, axisSub_X,
      hΘ (i + 1) (Nat.succ_pos i), hΘ' (i + 1) (Nat.succ_pos i)]
  refine AlgHom.ext fun f => ?_
  obtain ⟨g, rfl⟩ := axisSub_surjective hv0 hv1 f
  exact AlgHom.congr_fun key g

/-- **The constant-term homomorphism.** The `L`-algebra homomorphism sending `f` to the scalar
`constantCoeff f` acting on `Lambda L`. It is a legitimate candidate for a slope homomorphism at a
degenerate parameter, where `HJO.Sym.isSlopeHom_iff_of_degenerate` makes the prescription
`Θ`-free — and it kills every element of positive degree, which is what
`HJO.Mellit.lhsComputes_rhs_eq_zero_of_degenerate` uses. -/
noncomputable def constHom (L : Type*) [Field L] [Algebra ℚ L] :
    Lambda L →ₐ[L] Module.End L (Lambda L) :=
  (Algebra.ofId L (Module.End L (Lambda L))).comp (MvPolynomial.aeval fun _ => (0 : L))

/-- The constant-term homomorphism kills a homogeneous element of positive degree: such an element
has no constant term, and that is all `HJO.Sym.constHom` reads. -/
theorem constHom_eq_zero_of_mem_lambdaComp {N : ℕ} (hN : 0 < N) {f : Lambda L}
    (hf : f ∈ LambdaComp L N) : constHom L f = 0 := by
  have hc : MvPolynomial.constantCoeff f = 0 := by
    by_contra hne
    have := mem_lambdaComp.1 hf (congrFun MvPolynomial.constantCoeff_eq f ▸ hne)
    rw [Finsupp.weight_apply, Finsupp.sum_zero_index] at this
    omega
  rw [constHom, AlgHom.coe_comp, Function.comp_apply, MvPolynomial.aeval_zero', hc]
  simp

end HJO.Sym

namespace HJO.Mellit

open HJO.Sym HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {a b : ℕ}

/-! ### The sign bookkeeping of the bigrading -/

/-- **The sign arithmetic, over `ℕ` with truncated subtraction.** The bigrading
discrepancy `(-1)^{N(a+b)}` of `HJO.Dyck.Tilde.rel_biHomogeneous` turns the left-hand normalisation
`(-1)^{N(b+1)}` into `(-1)^{N(a+1)}`, and that is `(-1)^{(a-1)N}` — the exponent
`HJO.Mellit.LhsComputes` writes — because the two exponents differ by `2N` once `a ≥ 1`. -/
theorem neg_one_pow_bigrading {L : Type*} [Field L] (a b N : ℕ) (ha : 0 < a) :
    ((-1 : L)) ^ (N * (b + 1)) * (-1) ^ (N * (a + b)) = (-1) ^ ((a - 1) * N) := by
  rw [← pow_add]
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
  rw [Nat.add_sub_cancel,
    show N * (b + 1) + N * (c + 1 + b) = c * N + 2 * (N * b + N) by ring, pow_add, pow_mul]
  simp

/-- **`0 < a` is not decoration in the exponent.** At `a = 0` the truncated subtraction makes
`(a-1)N = 0`, while the bigrading produces `(-1)^{N(a+1)} = (-1)^N`; the two disagree at odd `N`.
`HJO.Mellit.lhsRewrite_sweepWitness_iff_lhsComputes` carries `0 < a`, so nothing reads the
statement there, but the exponent as written is not the identity without it. -/
theorem neg_one_pow_bigrading_ne_of_a_eq_zero :
    ((-1 : ℚ)) ^ ((0 - 1) * 1) ≠ (-1 : ℚ) ^ (1 * (0 + 1)) := by norm_num

/-! ### The creation seed of a one-part composition -/

/-- **The creation seed of a one-part composition.** `C_r(1) = (-q)^{1-r} h_r`: the displacement
`plethCreate` fixes the unit, so the pairing of `HJO.Sym.Cop` reads only the constant term of the
polynomial in `w` and returns the single complete homogeneous function. -/
theorem copComp_singleton_apply_one (q : L) (r : ℕ) :
    CopComp q [r] (1 : Lambda L) = MvPolynomial.C ((-q) ^ (1 - (r : ℤ))) * completeHomog L r := by
  rw [show CopComp q [r] = Cop q r from by rw [CopComp]; simp,
    show (1 : Lambda L) = elemSymm L 0 from (elemSymm_zero L).symm,
    HJO.CreationSeeds.cop_elemSymm]
  simp [elemSymm_zero]

/-- **The creation seed at `α = (1)` is `e_1`.** The scalar is `(-q)^0 = 1` and `h_1 = p_1 = e_1`.
-/
theorem copComp_one_apply_one (q : L) : CopComp q [1] (1 : Lambda L) = elemSymm L 1 := by
  rw [copComp_singleton_apply_one, HJO.CopPower.completeHomog_one, elemSymm_one]
  simp

/-- **A slope homomorphism is pinned on the seed of `α = (1)`, by the `k = 1` prescription alone.**
`C_1(1) = e_1 = -U_1` (`HJO.Sym.axisGen_one`), so `Θ (C_{(1)} 1) = -Q_{a,b}` for every slope
homomorphism -- no genericity beyond `qu ∉ {0, 1}`, which is what `axisGen_one` needs to evaluate
the scalar of `HJO.Sym.axisGen`. -/
theorem theta_copComp_one (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom a b q u Θ) :
    Θ (CopComp q [1] 1) = -Qop q u a b := by
  rw [copComp_one_apply_one, ← neg_neg (elemSymm L 1), ← axisGen_one hv0 hv1, map_neg,
    hΘ 1 Nat.one_pos]
  simp

/-! ### The right-hand side at a one-part composition -/

/-- **The stage word of a one-part composition is one stage.** -/
theorem stageWordTotal_singleton (q u : L) (a b A : ℕ) :
    stageWordTotal q u a b [A] = stageTotal q u a b 0 A 1 := by
  rw [stageWordTotal, stageFromTotal, stageFromTotal]

/-- **The stage word at `α = (1)`, written out.** No replicated letter occurs (`A - 1 = 0`), so
what is left is the descending train on `Ξ_{a,b}(-y_1 d^*_+)` applied to the vacuum. This is the
concrete word in sweep operators that `HJO.Mellit.qop_apply_one_of_lhsComputes` sets against
`Q_{a,b} 1`. -/
theorem stageWordTotal_singleton_one (q u : L) (a b : ℕ) :
    stageWordTotal q u a b [1]
      = -((-1 : L) ^ (a - 1) • trainDownEnd q 1 1
          (slopeOperator q u 1 a b (auxVar 1 * dplusStar q u 0 (1 : Total L)))) := by
  rw [stageWordTotal_singleton, stageTotal, Nat.sub_self, pow_zero, one_mul, replOneTotal]
  simp [LinearMap.mulLeft_apply]

/-! ### What the clause costs at `α = (1)` -/

/-- **`HJO.Mellit.LhsComputes` at its smallest instance.** Every quantifier is discharged: `N = 1`
and `α = (1)` force the seed, `HJO.Mellit.theta_copComp_one` forces `Θ` on it, and what survives is

`(-1)^b · ι(Q_{a,b} 1) = (-1)^{a-1} · ι(constantCoeff(lowerRun q 1 (stageWordTotal (1))))`.

The left-hand side is the slope operator of `HJO.Sym.Qop` on the symmetric functions; the right-hand
side, by `HJO.Mellit.stageWordTotal_singleton_one`, is a word in the sweep operators of
`HJO.Sweep.piece` read at the constant coefficient. So the clause asks for an identity between
`HJO.Sym.Qop` and a Carlsson--Mellit word already at `N = 1`, which is why no induction on `α`
reduces it: the bridge (`HJO.Sweep.exists_slopeActions` with
`HJO.Mellit.map_constantCoeff_markedWordOp'`, and `HJO.Dyck.Tilde.rel_biHomogeneous` for the sign)
is needed for the base case. -/
theorem qop_apply_one_of_lhsComputes (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom a b q u Θ)
    (h : LhsComputes q u a b) (ι : Lambda L →ₐ[L] AlphabetSeries L) (hι : IsRealisation ι) :
    (-1 : L) ^ b • ι (Qop q u a b (1 : Lambda L))
      = (-1 : L) ^ (a - 1) •
          ι (MvPolynomial.constantCoeff (lowerRun q 1 (stageWordTotal q u a b [1]))) := by
  have key := h ι hι Θ hΘ 1 Nat.one_pos [1] (by simp) (by simp)
  rw [theta_copComp_one hv0 hv1 hΘ] at key
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.cast_one, sub_self,
    zpow_zero, mul_one, one_mul] at key
  rw [LinearMap.neg_apply, map_neg, smul_neg, ← neg_smul,
    show -((-1 : L) ^ (b + 1)) = (-1) ^ b from by rw [pow_succ]; ring] at key
  exact key

/-- **At a degenerate parameter the clause says only that its own right-hand side vanishes.** If
`qu ∈ {0, 1}` and the slope operators `Q_{ak,bk}` do vanish — which by
`HJO.Sym.isSlopeHom_iff_of_degenerate` is exactly when `IsSlopeHom` is satisfiable there — then the
constant-term homomorphism `HJO.Sym.constHom` is a slope homomorphism, and it kills the creation
seed because `HJO.Sym.copComp_one_mem_lambdaComp` puts the seed in `Λ_N` with `N ≥ 1`. So the
clause's left-hand side is `0` at every composition, and `q ≠ 0` divides the scalar out of the
right.

This is the price of `HJO.Mellit.LhsComputes` carrying no hypothesis on `q` or `u`. It is not a
defect of the reduction — `LhsRewrite` quantifies over `Θ` identically, so the equivalence is
unaffected — but a proof of `LhsComputes` has to dispose of this regime, either by excluding
`qu ∈ {0, 1}` or by refuting `∀ k ≥ 1, Q_{ak,bk} = 0` there. -/
theorem lhsComputes_rhs_eq_zero_of_degenerate (hq : q ≠ 0) (hdeg : q * u = 0 ∨ q * u = 1)
    (hz : ∀ k : ℕ, 0 < k → Qop q u (a * k) (b * k) = 0) (h : LhsComputes q u a b)
    (ι : Lambda L →ₐ[L] AlphabetSeries L) (hι : IsRealisation ι)
    {N : ℕ} (hN : 0 < N) {α : List ℕ} (hpos : ∀ x ∈ α, 0 < x) (hsum : α.sum = N) :
    ι (MvPolynomial.constantCoeff (lowerRun q α.length (stageWordTotal q u a b α))) = 0 := by
  have hΘ : IsSlopeHom a b q u (constHom L) := (isSlopeHom_iff_of_degenerate hdeg _).2 hz
  have key := h ι hι (constHom L) hΘ N hN α hpos hsum
  rw [constHom_eq_zero_of_mem_lambdaComp hN (copComp_one_mem_lambdaComp q hsum)] at key
  simp only [LinearMap.zero_apply, map_zero, smul_zero] at key
  have hscal : ((-1 : L) ^ ((a - 1) * N) * q ^ ((α.length : ℤ) - (N : ℤ))) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (zpow_ne_zero _ hq)
  rcases smul_eq_zero.1 key.symm with h0 | h0
  · exact absurd h0 hscal
  · exact h0

end HJO.Mellit
