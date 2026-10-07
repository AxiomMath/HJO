/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.CriterionSufficient
public meta import HJO.Attr

/-! # The operator of a coefficient family, read as a functional of the displaced alphabet

The pairing of the proof of `HJO.Bglx.criterionNecessary` is
`⟨v⟩_k = ∑_α (v E_k)_α (Ξ_c)_{-α}`, with `v` ranging over the Laurent polynomials and `c` fixed.
The whole of that proof's Steps 1 to 3 is linear algebra in `v`: the hypothesis is read at
`v = δ^{(k)}(F)` and transported to `v = ζ_k(F)` by an identity between the two whose
`Λ`-coefficients do not depend on `k`.

This file records that functional in the form in which the linearity is free. Rather than the
symmetrised pairing — which needs the Stanton--Stembridge step to be recognised as one — it is
*literally* the constant term of a product formed in one cone ring,

`⟨v⟩_k = CT_k(v · E_k · Π_c Ω̂_k)`,

so that additivity and `Λ`-homogeneity are the additivity and `Λ`-homogeneity of a product and a
coefficient. `HJO.Bglx.dopWordOperator_eq_symbolCT` identifies it with the operator at
`v = δ^{(k)}(F)`, which is `HJO.Bglx.dopWordOperator_eq_ct` with the two factors regrouped.

## Main definitions

* `HJO.Bglx.symbolCT`: the functional `⟨·⟩_k` above.

## Main statements

* `HJO.Bglx.dopWordOperator_eq_symbolCT`: `V_c F = ⟨δ^{(k)}(F)⟩_k`.
* `HJO.Bglx.symbolCT_add`, `HJO.Bglx.symbolCT_sub`, `HJO.Bglx.symbolCT_laurentLambdaC_mul`,
  `HJO.Bglx.symbolCT_smul`: the linearity, which is all Steps 1 to 3 of the necessity argument
  use.

## Implementation notes

**The grouping matters and is chosen for the linearity, not for the operator.** With `E_k` attached
to `Π_c Ω̂_k` rather than to `v`, the functional is `v ↦ CT_k(ι(v) · W)` for the single fixed cone
ring element `W = E_k Π_c Ω̂_k`, so it is the composite of the ring homomorphism
`HJO.Bglx.laurentToCone`, multiplication by `W`, and the `Λ`-linear `HJO.Bglx.ct`. Regrouping
against `HJO.Bglx.dopWordOperator_eq_ct` costs one `mul_assoc`.

**`Λ`-homogeneity is stated at a constant Laurent polynomial**, `HJO.Bglx.laurentLambdaC`, because
that is the multiplier the transport identity produces: the coefficients of that identity are
symmetric functions, not scalars.

## References

F. Bergeron, A. M. Garsia, E. Leven and G. Xin, *Some remarkable new plethystic operators in the
theory of Macdonald polynomials*, arXiv:1405.0316v1, J. Comb. **7** (2016) 671--714, whose equation
(2.13) is the hypothesis read through the pairing `⟨·⟩_k` introduced in the proof of their
criterion. -/

@[expose] public section

namespace HJO.Bglx

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {k : ℕ}

/-- A symmetric function as a constant Laurent polynomial: the exponent-`0` monomial. This is the
multiplier the transport identity of the necessity proof produces. -/
noncomputable def laurentLambdaC (K : Type*) [CommRing K] (k : ℕ) :
    Lambda K →+* LaurentLambda K k :=
  AddMonoidAlgebra.singleZeroRingHom

@[simp] lemma laurentLambdaC_apply {K : Type*} [CommRing K] {k : ℕ} (a : Lambda K) :
    laurentLambdaC K k a = AddMonoidAlgebra.single 0 a := rfl

omit [Algebra ℚ L] in
/-- A constant Laurent polynomial, read in the cone ring, is the constant formal sum. -/
lemma laurentToCone_laurentLambdaC (τ : Equiv.Perm (Fin k)) (a : Lambda L) :
    laurentToCone τ (laurentLambdaC L k a) = ConeRing.const a := by
  refine ConeRing.ext (funext fun α => ?_)
  rw [coeff_laurentToCone, laurentLambdaC_apply, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply, ConeRing.coeff_const]
  exact if_congr eq_comm rfl rfl

/-- **The functional `⟨·⟩_k` of the necessity proof**: the constant term of `v E_k Π_c Ω̂_k`, formed
in the cone ring of the identity ordering. At `v = δ^{(k)}(F)` it is the operator of the coefficient
family applied to `F`. -/
noncomputable def symbolCT (q u : L) (k : ℕ) (c : (Fin k → ℕ) →₀ L) (v : LaurentLambda L k) :
    Lambda L :=
  ct k (Lambda L)
    (laurentToCone 1 v * (expAlphabet L k 1 * (symbolElem 1 c * kernelExpansion q u k))).coeff

/-- **The operator of a coefficient family is the functional at the displacement.** This is
`HJO.Bglx.dopWordOperator_eq_ct` with the exponential factor regrouped onto the symbol. -/
theorem dopWordOperator_eq_symbolCT (q u : L) (k : ℕ) (c : (Fin k → ℕ) →₀ L) (F : Lambda L) :
    dopWordOperator q u k c F = symbolCT q u k c (plethShiftMulti q u k F) := by
  rw [dopWordOperator_eq_ct q u k c F, symbolCT, shiftExpElem, mul_assoc]

/-! ### The linearity of the functional -/

/-- The constant term of a cone ring element, as a `Λ`-linear map. -/
noncomputable def ctElem (k : ℕ) (τ : Equiv.Perm (Fin k)) :
    ConeRing k τ (Lambda L) →ₗ[Lambda L] Lambda L :=
  (ct k (Lambda L)).comp (ConeRing.coeffLinear k τ (Lambda L))

omit [Algebra ℚ L] in
@[simp] lemma ctElem_apply (τ : Equiv.Perm (Fin k)) (x : ConeRing k τ (Lambda L)) :
    ctElem k τ x = ct k (Lambda L) x.coeff := rfl

theorem symbolCT_eq_ctElem (q u : L) (k : ℕ) (c : (Fin k → ℕ) →₀ L) (v : LaurentLambda L k) :
    symbolCT q u k c v
      = ctElem k 1
        (laurentToCone 1 v * (expAlphabet L k 1 * (symbolElem 1 c * kernelExpansion q u k))) := rfl

@[simp] theorem symbolCT_zero (q u : L) (k : ℕ) (c : (Fin k → ℕ) →₀ L) :
    symbolCT q u k c 0 = 0 := by
  rw [symbolCT_eq_ctElem, map_zero, zero_mul, map_zero]

theorem symbolCT_add (q u : L) (k : ℕ) (c : (Fin k → ℕ) →₀ L) (v w : LaurentLambda L k) :
    symbolCT q u k c (v + w) = symbolCT q u k c v + symbolCT q u k c w := by
  rw [symbolCT_eq_ctElem, symbolCT_eq_ctElem, symbolCT_eq_ctElem, map_add, add_mul, map_add]

theorem symbolCT_sub (q u : L) (k : ℕ) (c : (Fin k → ℕ) →₀ L) (v w : LaurentLambda L k) :
    symbolCT q u k c (v - w) = symbolCT q u k c v - symbolCT q u k c w := by
  rw [symbolCT_eq_ctElem, symbolCT_eq_ctElem, symbolCT_eq_ctElem, map_sub, sub_mul, map_sub]

/-- **The functional is homogeneous for a constant Laurent multiplier.** This is the step that lets
the transport identity of the necessity proof be applied with `Λ`-coefficients. -/
theorem symbolCT_laurentLambdaC_mul (q u : L) (k : ℕ) (c : (Fin k → ℕ) →₀ L) (a : Lambda L)
    (v : LaurentLambda L k) :
    symbolCT q u k c (laurentLambdaC L k a * v) = a * symbolCT q u k c v := by
  rw [symbolCT_eq_ctElem, symbolCT_eq_ctElem,
    map_mul (laurentToCone (1 : Equiv.Perm (Fin k))), laurentToCone_laurentLambdaC, mul_assoc,
    ← ConeRing.algebraMap_eq, ← Algebra.smul_def, map_smul, smul_eq_mul]

/-- **The functional is `𝕜`-homogeneous**, which is what divides the transport identity by the
nonzero scalar `κ(p_λ)`. -/
theorem symbolCT_smul (q u : L) (k : ℕ) (c : (Fin k → ℕ) →₀ L) (b : L)
    (v : LaurentLambda L k) : symbolCT q u k c (b • v) = b • symbolCT q u k c v := by
  have hb : (b • v : LaurentLambda L k) = laurentLambdaC L k (MvPolynomial.C b) * v := by
    rw [laurentLambdaC_apply, Algebra.smul_def]
    rfl
  rw [hb, symbolCT_laurentLambdaC_mul, Algebra.smul_def, MvPolynomial.algebraMap_eq]

end HJO.Bglx
