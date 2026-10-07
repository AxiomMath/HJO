/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Ascent.TransportSweep
public import HJO.Shuffle.MellitNablaPrime
public import HJO.Macdonald.PieriSupportFull
public import HJO.Collinear.PfunSupportDischarge

/-! # The ascent of the left-hand-side clause

The left-hand side of `HJO.Mellit.lhsRewrite_sweepWitness` compares two elements of `Λ`: the
slope-operator side `Θ(C_α 1) 1`, and the constant coefficient of the lowering run applied to the
stage word `G_{ℓ,α_ℓ} ⋯ G_{1,α_1}(1)` of the sweep witness. Both are built from operators defined
uniformly in the coefficient field, so along a homomorphism `φ : K → K'` of `ℚ`-algebras between
fields the identity at `(q, u)` is carried to the identity at `(φ q, φ u)`: the slope side by
`HJO.Ascent.lambdaMap_slopeHom` and `HJO.Ascent.lambdaMap_copComp`, the sweep side by
`HJO.Mellit.totalMap_stageWordTotal` and `HJO.Mellit.totalMap_lowerRun`.

Two points need care. First, the clause at `K'` quantifies over every slope homomorphism `Θ'` at
`(φ q, φ u)`, and the transported identity uses a slope homomorphism `Θ` at `(q, u)`. One exists:
the images under `Θ'` of the axis generators commute, the slope operators at `K` are carried to
those at `K'` by the injective map `HJO.Ascent.lambdaMap φ`, so the slope operators at `K` commute
and `HJO.Sym.exists_isSlopeHom` applies. Second, the base-case clause `HJO.Mellit.LhsSlope` is a
statement about every `f ∈ Λ^{K'}`, and the transport only reaches the image of `Λ^K`; both sides
are `K'`-linear in `f` and the image spans (`HJO.Ascent.span_range_lambdaMap`).

At the standing field `𝕜 = ℚ(q, u)` the base-case clause holds outright: the parameter inversion
`ι` is the bar involution `HJO.Sweep.lhsSlope_of_coprime_of_bar` asks for, the genericity
conditions are theorems, and the Macdonald conjugator normalised by `∇1 = 1` is the eigenoperator
of a modified Macdonald family, which fixes `H̃_∅`, a nonzero multiple of `1`. The ascent then
carries the clause to every field with an algebraically independent pair of parameters.

## Main results

* `HJO.Mellit.lhsWord_map`, `HJO.Mellit.lhsSlope_map`: the two clauses transport along any
  homomorphism of `ℚ`-algebras between fields, the first at an admissible instance.
* `HJO.Mellit.lhsWord_ascend`, `HJO.Mellit.lhsComputes_of_lhsWord_standing`: the clause
  `HJO.Mellit.LhsWord` at the standing field gives `HJO.Mellit.LhsComputes` at every field with an
  algebraically independent pair.
* `HJO.Sym.IsModifiedMacdonaldFamily.nablaOf_one`: the eigenoperator of a modified Macdonald family
  at generic parameters fixes `1`.
* `HJO.Sweep.lhsSlope_standing`, `HJO.Sweep.lhsSlope_of_algebraicIndependent`: the base-case clause
  at every positive coprime slope, at the standing field and at every algebraically independent
  pair, with no hypothesis.

## References

* [A. Mellit, *Toric braids and (m,n)-parking functions*][mellit2016], Section 3.7; the lemmas
  `HJO.Mellit.lhsRewrite_sweepWitness` and `HJO.Sweep.dop_eq_neg_dminusCM_auxVar_pow_dplusStar`.
-/

@[expose] public section

namespace HJO.Sym

/-- **The eigenoperator of a modified Macdonald family fixes `1`** at algebraically independent
parameters. -/
theorem IsModifiedMacdonaldFamily.nablaOf_one {L : Type*} [Field L] [Algebra ℚ L] {q u : L}
    (hqu : AlgebraicIndependent ℤ ![q, u]) {H : YoungDiagram → Lambda L}
    (h : IsModifiedMacdonaldFamily q u H) : nablaOf h 1 = 1 := by
  have hf : ∀ μ, Dop q u 0 (h.basis μ) = dopZeroEigenvalue q u μ • h.basis μ := fun μ => by
    rw [h.basis_apply]
    exact h.dop_zero μ
  have h1 : Dop q u 0 (1 : Lambda L) = dopZeroEigenvalue q u ⊥ • (1 : Lambda L) := by
    rw [HJO.DopCommutator.Witness.dop_zero_apply_one]
    simp [dopZeroEigenvalue, cellSum]
  obtain ⟨c, -, hc⟩ := h.basis.exists_smul_of_apply_eq_smul hf
    (fun μ ν hμν => eq_of_dopZeroEigenvalue_eq hqu hμν) one_ne_zero h1
  rw [h.basis_apply] at hc
  conv_lhs => rw [hc]
  rw [map_smul, isEigenoperator_nablaOf h ⊥, show cellProd q u ⊥ = 1 by simp [cellProd], one_smul,
    ← hc]

end HJO.Sym

namespace HJO.Mellit

open HJO.Sweep HJO.Sym HJO.Ascent

variable {K K' : Type*} [Field K] [Algebra ℚ K] [Field K'] [Algebra ℚ K']
variable (φ : K →ₐ[ℚ] K')

/-- **A commutation of slope operators descends** along a homomorphism of `ℚ`-algebras between
fields, the coefficient extension being injective and intertwining the slope operators. -/
theorem commute_qop_of_map {q u : K} {m n m' n' : ℕ}
    (h : Commute (Qop (φ q) (φ u) m n) (Qop (φ q) (φ u) m' n')) :
    Commute (Qop q u m n) (Qop q u m' n') := by
  refine LinearMap.ext fun f => ?_
  apply MvPolynomial.map_injective _ (φ : K →+* K').injective
  rw [← lambdaMap_apply, ← lambdaMap_apply, Module.End.mul_apply, Module.End.mul_apply,
    lambdaMap_qop, lambdaMap_qop, lambdaMap_qop, lambdaMap_qop]
  exact LinearMap.congr_fun h.eq _

/-- **A slope homomorphism descends**: if one exists at `(φ q, φ u)` then one exists at the
admissible instance `(q, u)`. -/
theorem exists_isSlopeHom_of_map {q u : K} (h : IsAdmissible q u) {a b : ℕ}
    {Θ' : Lambda K' →ₐ[K'] Module.End K' (Lambda K')} (hΘ' : IsSlopeHom a b (φ q) (φ u) Θ') :
    ∃ Θ : Lambda K →ₐ[K] Module.End K (Lambda K), IsSlopeHom a b q u Θ := by
  have := HJO.Ascent.charZero_of_algebra_rat K
  refine HJO.Sym.exists_isSlopeHom (mul_ne_zero h.fst_ne_zero h.snd_ne_zero)
    h.mul_pow_succ_ne_one fun k l hk hl => commute_qop_of_map φ ?_
  rw [← hΘ' k hk, ← hΘ' l hl, ← map_mul]
  exact (Commute.all _ _).map Θ'

/-- **The clause `HJO.Mellit.LhsWord` transports** along a homomorphism of `ℚ`-algebras between
fields, from an admissible instance. -/
theorem lhsWord_map {q u : K} (h : IsAdmissible q u) {a b : ℕ} (hw : LhsWord q u a b) :
    LhsWord (φ q) (φ u) a b := by
  intro Θ' hΘ' N hN α hpos hsum
  obtain ⟨Θ, hΘ⟩ := exists_isSlopeHom_of_map φ h hΘ'
  have key := congrArg (lambdaMap φ) (hw Θ hΘ N hN α hpos hsum)
  rw [lambdaMap_smul, lambdaMap_smul, lambdaMap_slopeHom φ h hΘ hΘ', lambdaMap_copComp,
    map_one (lambdaMap φ),
    ← constantCoeff_totalMap_eq_lambdaMap, totalMap_lowerRun, totalMap_stageWordTotal] at key
  simpa only [map_mul, map_pow, map_neg, map_one, map_zpow₀, RingHom.coe_coe,
    AlgHom.coe_toRingHom] using key

/-- **The base-case clause `HJO.Mellit.LhsSlope` transports** along any homomorphism of
`ℚ`-algebras between fields, with no hypothesis. -/
theorem lhsSlope_map {q u : K} {a b : ℕ} (hs : LhsSlope q u a b) : LhsSlope (φ q) (φ u) a b := by
  intro g
  have hg : g ∈ Submodule.span K' (Set.range (lambdaMap φ)) := by
    rw [span_range_lambdaMap]
    trivial
  refine (?_ : Submodule.span K' (Set.range (lambdaMap φ)) ≤ lhsSlopeCarrier (φ q) (φ u) a b) hg
  rw [Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  change LhsSlopeAt (φ q) (φ u) a b (lambdaMap φ f)
  have key := congrArg (totalMap (φ : K →+* K')) (hs f)
  rw [totalMap_C_eq_lambdaMap, lambdaMap_qop, totalMap_smul, totalMap_dminus,
    totalMap_slopeOperator, totalMap_slopeArg, ← lambdaMap_apply] at key
  simp only [map_pow, map_neg, map_one, RingHom.coe_coe] at key
  exact key

section Ascend

variable (K : Type*) [Field K] [Algebra ℚ K] [Algebra ParamRing K] [IsFractionRing ParamRing K]
variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The clause `HJO.Mellit.LhsWord` ascends** from the standing field to any field with an
algebraically independent pair of parameters, at every slope. -/
theorem lhsWord_ascend {x y : L} (h : AlgebraicIndependent ℤ ![x, y]) {a b : ℕ}
    (hw : LhsWord (paramQ K) (paramU K) a b) : LhsWord x y a b := by
  have key := lhsWord_map (ascend K h) (isAdmissible_standing K) hw
  rwa [ascend_paramQ, ascend_paramU] at key

/-- If `HJO.Mellit.LhsWord` holds at the standing field at every coprime slope `1 < a < b`, then
`HJO.Mellit.LhsComputes q u a b` holds at every algebraically independent pair `(q, u)` and every
such slope. -/
theorem lhsComputes_of_lhsWord_standing
    (hw : ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b → LhsWord (paramQ K) (paramU K) a b) :
    ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b →
      LhsComputes q u a b :=
  fun _ _ hqu a b hab ha hlt => lhsComputes_of_lhsWord (lhsWord_ascend K hqu (hw a b hab ha hlt))

end Ascend

end HJO.Mellit

namespace HJO.Sweep

open HJO.Sym HJO.Ascent HJO.Standing

section Standing

variable (K : Type*) [Field K] [Algebra ℚ K] [Algebra ParamRing K] [IsFractionRing ParamRing K]

/-- **The Macdonald conjugator normalised by `∇1 = 1` exists at the standing field.** It is the
eigenoperator of the modified Macdonald family, which exists at `𝕜` with no hypothesis. -/
theorem exists_isMacdonaldConjugator_one_param :
    ∃ nabla : Module.End K (Lambda K),
      IsMacdonaldConjugator (paramQ K) (paramU K) nabla ∧ nabla 1 = 1 := by
  have hqu := algebraicIndependent_param K
  obtain ⟨H, hH⟩ := exists_isModifiedMacdonaldFamily_of_hasPieriEigenfamily hqu
    (paramQUInvHom_paramQ K) (paramQUInvHom_paramU K) (paramQUInvHom_involutive K)
    (HJO.Ascent.ringHom_algebraMap_rat (paramQUInvHom K))
    (hasUnnormalisedMacdonaldEigenbasis_param K)
    (hasPieriEigenfamily_param K (hasPfunPieriSupport_param K))
  have hn := isEigenoperator_nablaOf hH
  have hq := paramQ_ne_zero K
  have hu := paramU_ne_zero K
  have hM := paramProduct_param_ne_zero K
  exact ⟨nablaOf hH,
    { bijective := bijective_of_isEigenoperator hq hu hH hn
      map_dop_zero := nabla_dop_zero hH hn
      map_elemSymm_one_mul := nabla_elemSymm_one_mul hM hH hn
      map_dopStar_one := nabla_dopStar_one hq hu hM hH hn },
    hH.nablaOf_one hqu⟩

/-- **The base-case clause of `HJO.Mellit.lhsRewrite_sweepWitness` at the standing field**, at every
positive coprime slope and with no hypothesis: `HJO.Sweep.lhsSlope_of_coprime_of_bar` with the
parameter inversion `ι` as the bar involution and the normalised Macdonald conjugator of
`HJO.Sweep.exists_isMacdonaldConjugator_one_param`. -/
theorem lhsSlope_standing :
    ∀ a b : ℕ, Nat.Coprime a b → 1 ≤ a → 1 ≤ b →
      HJO.Mellit.LhsSlope (paramQ K) (paramU K) a b := by
  have : Invertible (paramQ K) := invertibleOfNonzero (paramQ_ne_zero K)
  have : Invertible (paramU K) := invertibleOfNonzero (paramU_ne_zero K)
  have : Invertible (paramQ K - 1) :=
    invertibleOfNonzero (sub_ne_zero.2 (by simpa using paramQ_pow_succ_ne_one K 0))
  refine lhsSlope_of_coprime_of_bar (fun k hk => ?_) ?_ (bar := (paramQUInv K).toRingEquiv)
    ?_ ?_ (paramQUInv_involutive K) (exists_isMacdonaldConjugator_one_param K)
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact mul_ne_zero (sub_ne_zero.2 (paramQ_pow_succ_ne_one K j).symm)
      (sub_ne_zero.2 (paramU_pow_succ_ne_one K j).symm)
  · intro h0
    apply paramQ_pow_succ_ne_one K 1
    rw [eq_neg_of_add_eq_zero_left h0]
    norm_num
  all_goals simp [invOf_eq_inv]

end Standing

/-- **The base-case clause of `HJO.Mellit.lhsRewrite_sweepWitness` at every algebraically
independent pair**, at every positive coprime slope and with no further hypothesis: the clause at
the standing field (`HJO.Sweep.lhsSlope_standing`) carried along the ascent by
`HJO.Mellit.lhsSlope_map`. -/
theorem lhsSlope_of_algebraicIndependent {L : Type*} [Field L] [Algebra ℚ L] :
    ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ a b : ℕ, Nat.Coprime a b → 1 ≤ a → 1 ≤ b →
      HJO.Mellit.LhsSlope q u a b := by
  intro q u hqu a b hab ha hb
  have key := HJO.Mellit.lhsSlope_map (ascend Kk hqu) (lhsSlope_standing Kk a b hab ha hb)
  rwa [ascend_paramQ, ascend_paramU] at key

end HJO.Sweep

end
