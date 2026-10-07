/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.ConjugationOperator
public import HJO.CarlssonMellit.DminusSquare
public import HJO.CarlssonMellit.DopFromDplusStar
public import HJO.CarlssonMellit.DoubleShift
public import HJO.Collinear.OmegaBarDop
public import HJO.Collinear.Vocabulary
public import HJO.Macdonald.ReachStar
public import HJO.Shuffle.Grading
public meta import HJO.Attr

/-! # The conjugation operator on the bottom module

`HJO.Sweep.conjugation_eq_signGrading_conjugator_omegaBar`, Theorem 7.4(iii) of Carlsson--Mellit: a
conjugation operator `𝒩` acts on `Λ = V_0` as `f ↦ ε_±(∇(ω̄ f))`, for any Macdonald conjugator `∇`
preserving the homogeneous components and fixing `1`.

## The shape of the statement

`𝒩` is an endomorphism of `V_* = ⨁_k V_k` while `∇`, `ε_±` and `ω̄` are endomorphisms of `Λ`, so the
two sides are compared in `V_*` along `HJO.Sweep.vzero`, the inclusion of `Λ` as the zeroth summand.
Read that way the statement carries the preservation of `V_0` as well as the formula: it says that
`𝒩` applied to the zeroth summand lands back in the zeroth summand, and names the element.

## Why the usual opening step is not the argument used

The proof as usually written opens by asserting that `𝒩` carries each summand `V_k` to itself,
deducing it from the five clauses of `HJO.Sweep.IsConjugationOperator` "because those operators
shift the index by `±1` in the same way". That deduction does not go through as stated, and the
obstruction is exactly the one `HJO.Sweep.IsConjugationOperator`'s own docstring records: the two
intertwining clauses are quantified over the summands, so the step

  `𝒩𝒩 = id` and `𝒩d_+ = d_+^*𝒩`  give  `𝒩d_+^* = d_+𝒩`

is available only where `𝒩` is *already* known to map a summand into a summand. Applying `𝒩` to
`𝒩(d_+F) = d_+^*(𝒩F)` gives `d_+F = 𝒩(d_+^*(𝒩F))`, and to substitute `F := 𝒩F` one needs `𝒩F` to sit
in a summand, which is the very thing being derived.

The repair costs nothing and is the reason the induction below is run in the shape it is. The
predicate cut out on `Λ` is

  `W = {f : 𝒩(vzero(ω̄ f)) = vzero(ε_±(∇ f))}`,

whose membership *asserts* that `𝒩(vzero(ω̄ f))` lies in the zeroth summand. So at each step of the
`HJO.Sym.eq_top_of_one_mem_of_closed` induction the summand-preservation needed for the `d_+^*`
clause is supplied by the inductive hypothesis, and `HJO.Sweep.conj_dplusStar_vzero_of_eq` is that
local form of it. No global preservation of the summands is assumed anywhere, and none is proved:
what comes out is the preservation of `V_0` alone, which is all the statement needs and all the
consumers use.

## The side condition

`hM : HJO.Sym.paramProduct q u ≠ 0`, i.e. `(1 - q)(1 - u) ≠ 0`. The reachability statement
`HJO.Sym.eq_top_of_one_mem_of_closed` is usually given with no hypothesis; its Lean form carries
this one, inherited from `HJO.Sym.dopStar_mem_reachStar`, whose proof divides by `M̃`. It is free at
every consumer, `q` and `u` being algebraically independent there.

## Main definitions

* `HJO.Sweep.vzero`: `Λ` as the zeroth summand of `V_*`.

## Main results

* `HJO.Sweep.conjugation_eq_signGrading_conjugator_omegaBar`.

## References

The lemma `HJO.Sweep.conjugation_eq_signGrading_conjugator_omegaBar` on the Dyck path algebra and
the involution, using `HJO.Sweep.IsConjugationOperator`, `HJO.Sym.IsMacdonaldConjugator`,
`HJO.Sym.omegaBar`, `HJO.Sym.signGrading`, and the inputs `HJO.Sweep.dminusCM_cmDPlus_C`,
`HJO.Sweep.dop_one_eq_neg_dminusCM_dplusStar`, `HJO.Sym.omegaBar_dop`,
`HJO.Sym.eq_top_of_one_mem_of_closed`.
-/

@[expose] public section

namespace HJO.Sweep

open HJO.Sym

/-! ### `Λ` as the zeroth summand -/

section Vzero

variable {L : Type*} [CommRing L]

/-- An element of `Λ` read as a constant lies in `V_0`: the zeroth piece is the image of the
structure map, `HJO.Sweep.piece` reading `V_0 = Λ ⊗ 𝕜[]`. -/
theorem C_mem_pieceSub_zero (f : Lambda L) : (MvPolynomial.C f : Total L) ∈ pieceSub L 0 := by
  rw [← MvPolynomial.algebraMap_eq]
  exact (piece L 0).algebraMap_mem f

/-- `Λ` as the zeroth graded piece, `L`-linearly. -/
noncomputable def zeroPiece (L : Type*) [CommRing L] : Lambda L →ₗ[L] pieceSub L 0 where
  toFun f := ⟨MvPolynomial.C f, C_mem_pieceSub_zero f⟩
  map_add' f g := by ext; simp
  map_smul' c f := by
    refine Subtype.ext ?_
    change MvPolynomial.C (c • f) = c • (MvPolynomial.C f : Total L)
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    rfl

@[simp]
theorem coe_zeroPiece (f : Lambda L) :
    (zeroPiece L f : Total L) = MvPolynomial.C f := rfl

/-- **`Λ = V_0` as the zeroth summand of `V_*`.** This is the map along which
`HJO.Sweep.conjugation_eq_signGrading_conjugator_omegaBar` compares an endomorphism of `V_*` with
one of `Λ`. -/
noncomputable def vzero (L : Type*) [CommRing L] : Lambda L →ₗ[L] Vstar L :=
  (ofPiece L 0).comp (zeroPiece L)

theorem vzero_apply (f : Lambda L) : vzero L f = ofPiece L 0 (zeroPiece L f) := rfl

end Vzero

section VzeroOne

variable {L : Type*} [Field L]

/-- The inclusion of `Λ` as the zeroth summand carries `1` to the `1` of `𝒩(1) = 1`. -/
@[simp]
theorem vzero_one : vzero L (1 : Lambda L) = oneVstar L :=
  congrArg (ofPiece L 0) (Subtype.ext (by simp))

end VzeroOne

/-! ### The two composites of the raising and lowering operators on `V_0` -/

section Composites

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`d_-d_+` is multiplication by `e_1` on `V_0`**, read in `V_*`: `HJO.Sweep.dminusCM_cmDPlus_C`
with the two operators assembled as endomorphisms of the direct sum. -/
theorem dminusVstar_cmDPlusVstar_vzero (q : L) (f : Lambda L) :
    dminusVstar q (cmDPlusVstar q (vzero L f)) = vzero L (elemSymm L 1 * f) := by
  rw [vzero_apply, cmDPlusVstar_ofPiece, dminusVstar_ofPiece, vzero_apply]
  exact congrArg (ofPiece L 0) (Subtype.ext (by
    rw [coe_dminusPiece, coe_cmDPlusPiece, coe_zeroPiece, coe_zeroPiece, dminusCM_cmDPlus_C]))

/-- **`d_-d_+^*` is `-D_1` on `V_0`**, read in `V_*`: `HJO.Sweep.dop_one_eq_neg_dminusCM_dplusStar`
with the two operators assembled as endomorphisms of the direct sum. -/
theorem dminusVstar_dplusStarVstar_vzero (q u : L) (f : Lambda L) :
    dminusVstar q (dplusStarVstar q u (vzero L f)) = vzero L (-Dop q u 1 f) := by
  rw [vzero_apply, dplusStarVstar_ofPiece, dminusVstar_ofPiece, vzero_apply]
  refine congrArg (ofPiece L 0) (Subtype.ext ?_)
  rw [coe_dminusPiece, coe_dplusStarPiece, coe_zeroPiece, coe_zeroPiece, map_neg,
    dop_one_eq_neg_dminusCM_dplusStar, neg_neg]

end Composites

/-! ### The conjugate involution against the sign of the grading -/

section OmegaBar

variable {L : Type*} [CommRing L]

/-- **`ω̄` is an involution** when the bar of the base is: it negates each generator and moves each
scalar by `σ`, so two applications restore both. This is `HJO.Sym.omegaBar` read through
`HJO.Sym.plethNegate` and `HJO.Sym.paramInvLambda`, the "`ω̄` being an involution". -/
theorem omegaBar_omegaBar {σ : L ≃+* L} (hσ : ∀ c, σ (σ c) = c) (f : Lambda L) :
    omegaBar σ (omegaBar σ f) = f := by
  have key : (omegaBar σ : Lambda L →+* Lambda L).comp (omegaBar σ) = RingHom.id (Lambda L) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, omegaBar_C, omegaBar_C, hσ, RingHom.id_apply]
    · rw [RingHom.comp_apply, omegaBar_X, map_neg, omegaBar_X, neg_neg, RingHom.id_apply]
  exact congrArg (fun g : Lambda L →+* Lambda L => g f) key

/-- **`ω̄` is antilinear over `σ`**: it moves a scalar by `σ`, `HJO.Sym.paramInvLambda` doing that
and `ω₋` being unital. -/
theorem omegaBar_smul (σ : L ≃+* L) (c : L) (f : Lambda L) :
    omegaBar σ (c • f) = σ c • omegaBar σ f := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, omegaBar_C, MvPolynomial.smul_eq_C_mul]

variable [Algebra ℚ L]

/-- **`ω̄` negates `e_1`**: `e_1 = p_1`, which `cj` fixes and `ω₋` negates. -/
theorem omegaBar_elemSymm_one_mul (σ : L ≃+* L) (f : Lambda L) :
    omegaBar σ (elemSymm L 1 * f) = -(elemSymm L 1 * omegaBar σ f) := by
  rw [map_mul, elemSymm_one, powerSum, omegaBar_X, neg_mul]

end OmegaBar

/-! ### The two relations satisfied by `ε_±∇` -/

section SignConjugator

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}
  {nabla : Module.End L (Lambda L)} (hnabla : IsMacdonaldConjugator q u nabla)
  (hcomp : ∀ n : ℕ, ∀ f ∈ LambdaComp L n, nabla f ∈ LambdaComp L n)

include hnabla hcomp

/-- **`ε_±∇` turns multiplication by `e_1` into `D_1`**, on a homogeneous element. `∇` sends `e_1f`
to `-D_1∇f` by `HJO.Sym.IsMacdonaldConjugator`, and `e_1f` is homogeneous one degree up, so the sign
`ε_±` contributes is the opposite of the one it contributes at `f`; the two negations cancel. -/
theorem signGrading_conjugator_elemSymm_one_mul_of_mem {n : ℕ} {f : Lambda L}
    (hf : f ∈ LambdaComp L n) :
    signGrading L (nabla (elemSymm L 1 * f)) = Dop q u 1 (signGrading L (nabla f)) := by
  have hmul : elemSymm L 1 * f ∈ LambdaComp L (1 + n) :=
    mul_mem_lambdaComp (elemSymm_mem_lambdaComp L 1) hf
  rw [signGrading_of_mem_lambdaComp (hcomp _ _ hmul),
    signGrading_of_mem_lambdaComp (hcomp _ _ hf), map_smul,
    hnabla.map_elemSymm_one_mul, pow_add, pow_one, mul_smul, neg_smul, one_smul, smul_neg, neg_neg]

/-- **`ε_±∇` turns `D^*_1` into minus multiplication by `e_1`**, on a homogeneous element. `∇` sends
`D^*_1f` to `e_1∇f` by `HJO.Sym.IsMacdonaldConjugator`, which is homogeneous one degree up, so `ε_±`
contributes the opposite sign there and the statement carries the difference. -/
theorem signGrading_conjugator_dopStar_one_of_mem {n : ℕ} {f : Lambda L}
    (hf : f ∈ LambdaComp L n) :
    signGrading L (nabla (DopStar q u 1 f)) = -(elemSymm L 1 * signGrading L (nabla f)) := by
  have hmul : elemSymm L 1 * nabla f ∈ LambdaComp L (1 + n) :=
    mul_mem_lambdaComp (elemSymm_mem_lambdaComp L 1) (hcomp _ _ hf)
  rw [hnabla.map_dopStar_one, signGrading_of_mem_lambdaComp hmul,
    signGrading_of_mem_lambdaComp (hcomp _ _ hf), mul_smul_comm, pow_add, pow_one, mul_smul,
    neg_smul, one_smul]

/-- **`ε_±∇` turns multiplication by `e_1` into `D_1`**, at every element of `Λ`. Both sides are
`L`-linear, so the homogeneous case suffices: `Λ` is spanned by its monomials, each weighted
homogeneous of its own degree. -/
theorem signGrading_conjugator_elemSymm_one_mul (f : Lambda L) :
    signGrading L (nabla (elemSymm L 1 * f)) = Dop q u 1 (signGrading L (nabla f)) := by
  rw [f.as_sum, Finset.mul_sum]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  exact signGrading_conjugator_elemSymm_one_mul_of_mem hnabla hcomp
    (mem_lambdaComp.2 (MvPolynomial.isWeightedHomogeneous_monomial _ e _ rfl))

/-- **`ε_±∇` turns `D^*_1` into minus multiplication by `e_1`**, at every element of `Λ`, by the
same linearity. -/
theorem signGrading_conjugator_dopStar_one (f : Lambda L) :
    signGrading L (nabla (DopStar q u 1 f)) = -(elemSymm L 1 * signGrading L (nabla f)) := by
  rw [f.as_sum]
  simp only [map_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  exact signGrading_conjugator_dopStar_one_of_mem hnabla hcomp
    (mem_lambdaComp.2 (MvPolynomial.isWeightedHomogeneous_monomial _ e _ rfl))

end SignConjugator

/-! ### The starred raising clause where `𝒩` is known to preserve the zeroth summand -/

section Conjugation

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {σ : L ≃+* L}
  {N : Vstar L →+ Vstar L}

/-- **`𝒩d_+^* = d_+𝒩` on the zeroth summand, wherever `𝒩` is known to map it there.** This is the
step "`𝒩𝒩 = id` and `𝒩d_+ = d_+^*𝒩` give `𝒩d_+^* = d_+𝒩`", stated with the hypothesis
that step actually needs: `HJO.Sweep.IsConjugationOperator` quantifies its intertwining clauses over
the summands, so the substitution `F := 𝒩F` is licensed only once `𝒩F` is itself in a summand.

Given `𝒩(vzero g) = vzero h`, involutivity gives `𝒩(vzero h) = vzero g`; the `d_+` clause at `h`
then reads `𝒩(d_+(vzero h)) = d_+^*(vzero g)`, and applying `𝒩` once more turns it into the
assertion. -/
theorem conj_dplusStar_vzero_of_eq (hN : IsConjugationOperator q u σ N) {g h : Lambda L}
    (hgh : N (vzero L g) = vzero L h) :
    N (dplusStarVstar q u (vzero L g)) = cmDPlusVstar q (vzero L h) := by
  have hhg : N (vzero L h) = vzero L g := by rw [← hgh, hN.involutive]
  have hstep : N (cmDPlusVstar q (vzero L h)) = dplusStarVstar q u (vzero L g) := by
    rw [vzero_apply, hN.map_dplus 0, ← vzero_apply, hhg, vzero_apply]
  rw [← hstep, hN.involutive]

/-- **`𝒩` carries multiplication by `e_1` on `V_0` to `d_-d_+^*𝒩`.** `e_1` is `d_-d_+` on `V_0` by
`HJO.Sweep.dminusCM_cmDPlus_C`, and the two clauses of `HJO.Sweep.IsConjugationOperator` apply in
turn, each at the summand its argument sits in. Nothing about `𝒩` preserving the summands is
used. -/
theorem conj_vzero_elemSymm_one_mul (hN : IsConjugationOperator q u σ N) (g : Lambda L) :
    N (vzero L (elemSymm L 1 * g)) = dminusVstar q (dplusStarVstar q u (N (vzero L g))) := by
  have h1 : N (vzero L (elemSymm L 1 * g))
      = dminusVstar q (N (cmDPlusVstar q (vzero L g))) := by
    rw [← dminusVstar_cmDPlusVstar_vzero q, vzero_apply, cmDPlusVstar_ofPiece,
      hN.map_dminus 0 (cmDPlusPiece q 0 (zeroPiece L g)), ← cmDPlusVstar_ofPiece, ← vzero_apply]
  rw [h1, vzero_apply, hN.map_dplus 0]

/-- **`𝒩` carries `-D_1` on `V_0` to multiplication by `e_1`, wherever it is known to preserve the
zeroth summand.** `-D_1` is `d_-d_+^*` on `V_0` by `HJO.Sweep.dop_one_eq_neg_dminusCM_dplusStar`;
the `d_-` clause applies outright and the `d_+^*` one through
`HJO.Sweep.conj_dplusStar_vzero_of_eq`, which is where the hypothesis `hgh` is spent. -/
theorem conj_vzero_neg_dop_one (hN : IsConjugationOperator q u σ N) {g h : Lambda L}
    (hgh : N (vzero L g) = vzero L h) :
    N (vzero L (-Dop q u 1 g)) = vzero L (elemSymm L 1 * h) := by
  rw [← dminusVstar_dplusStarVstar_vzero q u, vzero_apply, dplusStarVstar_ofPiece,
    hN.map_dminus 0 (dplusStarPiece q u 0 (zeroPiece L g)), ← dplusStarVstar_ofPiece,
    ← vzero_apply, conj_dplusStar_vzero_of_eq hN hgh, dminusVstar_cmDPlusVstar_vzero]

/-- **Carlsson--Mellit, the conjugation operator on the bottom module.** For a
conjugation operator `𝒩` and a Macdonald conjugator `∇` preserving each homogeneous component of
`Λ` and fixing `1`, `𝒩(f) = ε_±(∇(ω̄ f))` for every `f ∈ Λ = V_0`.

The proof runs on the predicate

  `W = {f : 𝒩(vzero(ω̄ f)) = vzero(ε_±(∇ f))}`.

`W` is an `L`-submodule because `ω̄` and `𝒩` are each antilinear over `σ` and `σ` is an involution,
so their composite is linear. It contains `1`, `ω̄` and `∇` and `ε_±` all fixing it and `𝒩(1) = 1`.
It is closed under multiplication by `e_1` and under `D^*_1`, by the four relations
`HJO.Sweep.dminusCM_cmDPlus_C`, `HJO.Sweep.dop_one_eq_neg_dminusCM_dplusStar`,
`HJO.Sym.omegaBar_dop` and the two `ε_±∇` relations above -- and, for the `D^*_1` step, by
`HJO.Sweep.conj_dplusStar_vzero_of_eq`, whose hypothesis is exactly membership in `W`. So
`HJO.Sym.eq_top_of_one_mem_of_closed` makes `W` all of `Λ`, and the conclusion is that statement at
`ω̄ f`, `ω̄` being an involution. -/
@[hjo "lem_cm_thm74iii"]
theorem conjugation_eq_signGrading_conjugator_omegaBar (hσ : ∀ c, σ (σ c) = c) (hq : σ q = q⁻¹)
    (hu : σ u = u⁻¹) (hM : paramProduct q u ≠ 0) (hN : IsConjugationOperator q u σ N)
    {nabla : Module.End L (Lambda L)} (hnabla : IsMacdonaldConjugator q u nabla)
    (hcomp : ∀ n : ℕ, ∀ f ∈ LambdaComp L n, nabla f ∈ LambdaComp L n) (hone : nabla 1 = 1)
    (f : Lambda L) :
    N (vzero L f) = vzero L (signGrading L (nabla (omegaBar σ f))) := by
  set W : Submodule L (Lambda L) :=
    { carrier := {g | N (vzero L (omegaBar σ g)) = vzero L (signGrading L (nabla g))}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_add, map_add, map_add, map_add, map_add, map_add, ha, hb]
      zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [omegaBar_smul, map_smul, hN.map_smul, hσ, ha, map_smul, map_smul, map_smul] } with hW
  have hmem : ∀ g : Lambda L,
      g ∈ W ↔ N (vzero L (omegaBar σ g)) = vzero L (signGrading L (nabla g)) := fun _ => Iff.rfl
  -- `1 ∈ W`
  have hone_mem : (1 : Lambda L) ∈ W := by
    rw [hmem, map_one, vzero_one, hN.map_one, hone, map_one, vzero_one]
  -- `ω̄` is antilinear and `𝒩` is additive, so the negated instance of the hypothesis is available;
  -- every sign below is carried inside `Λ`, `V_*` having no `Neg` instance here.
  have hnegmem : ∀ g ∈ W, N (vzero L (omegaBar σ (-g))) = vzero L (signGrading L (nabla (-g))) :=
    fun g hg => (hmem (-g)).1 (W.neg_mem hg)
  -- closure under multiplication by `e₁`
  have helem : ∀ g ∈ W, elemSymm L 1 * g ∈ W := by
    intro g hg
    rw [hmem]
    calc N (vzero L (omegaBar σ (elemSymm L 1 * g)))
        = N (vzero L (elemSymm L 1 * omegaBar σ (-g))) := by
          rw [map_neg, mul_neg, omegaBar_elemSymm_one_mul]
      _ = dminusVstar q (dplusStarVstar q u (vzero L (signGrading L (nabla (-g))))) := by
          rw [conj_vzero_elemSymm_one_mul hN, hnegmem g hg]
      _ = vzero L (signGrading L (nabla (elemSymm L 1 * g))) := by
          rw [dminusVstar_dplusStarVstar_vzero,
            signGrading_conjugator_elemSymm_one_mul hnabla hcomp]
          exact congrArg (vzero L) (by simp only [map_neg, neg_neg])
  -- closure under `D*₁`
  have hdop : ∀ g ∈ W, DopStar q u 1 g ∈ W := by
    intro g hg
    rw [hmem]
    have hrw : omegaBar σ (DopStar q u 1 g) = -Dop q u 1 (omegaBar σ (-g)) := by
      have h := omegaBar_dop hq hu 1 (omegaBar σ g)
      rw [omegaBar_omegaBar hσ] at h
      rw [map_neg, map_neg, neg_neg, ← h, omegaBar_omegaBar hσ]
    rw [hrw, conj_vzero_neg_dop_one hN (hnegmem g hg),
      signGrading_conjugator_dopStar_one hnabla hcomp]
    exact congrArg (vzero L) (by simp only [map_neg, mul_neg])
  have htop : W = ⊤ := eq_top_of_one_mem_of_closed hM hone_mem helem hdop
  have hall : ∀ g : Lambda L, N (vzero L (omegaBar σ g)) = vzero L (signGrading L (nabla g)) :=
    fun g => (hmem g).1 (htop ▸ Submodule.mem_top)
  have h := hall (omegaBar σ f)
  rwa [omegaBar_omegaBar hσ] at h

end Conjugation

end HJO.Sweep
