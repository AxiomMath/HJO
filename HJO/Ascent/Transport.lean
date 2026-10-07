/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Ascent.Admissible
public import HJO.Collinear.DopStarPair
public import HJO.Collinear.ShiftPair
public import HJO.Evaluation.PhiE
public import HJO.Symmetric.UkRegular
public meta import HJO.Attr

/-!
# Transport of the symmetric-function operators along a coefficient homomorphism

Let `φ : K →ₐ[ℚ] K'` be a homomorphism of `ℚ`-algebras between fields. The coefficient extension
`Λ_φ : Λ^K → Λ^{K'}` is the ring homomorphism restricting to `φ` on `K` and fixing every power sum
`p_k`. It carries the complete homogeneous and elementary symmetric functions, the plethystic
displacement, the basic operators `D_k` and the slope operators at parameters `(q, u)` to their
counterparts at `(φ q, φ u)`. Since the image of `Λ_φ` spans `Λ^{K'}` over `K'`, a commuting pair
of operators over `K` intertwined with a pair over `K'` forces the latter to commute.

## Main definitions

* `lambdaMap`: The coefficient extension `Λ_φ : Λ^K → Λ^{K'}`.
* `laurentMap`: The coefficientwise extension of `Λ_φ` to polynomials over `Λ^K`.

## Main results

* `span_range_lambdaMap`: The image of `Λ_φ` spans `Λ^{K'}` as a `K'`-vector space.
* `lambdaMap_mem_lambdaComp`: `Λ_φ` preserves the grading.
* `lambdaMap_completeHomog`, `lambdaMap_elemSymm`: `Λ_φ` fixes `h_n` and `e_n`.
* `laurentMap_plethShift`: The coefficient extension commutes with the plethystic displacement.
* `lambdaMap_dop`: `Λ_φ` intertwines the basic operators.
* `lambdaMap_qop`: `Λ_φ` intertwines the slope operators.
* `commute_of_intertwined`: Two `K'`-linear endomorphisms intertwined along `Λ_φ` with a commuting
  pair of `K`-linear endomorphisms commute.
* `commute_qop_map`: Slope operators commuting at `(q, u)` commute at `(φ q, φ u)`.

## Implementation notes

`Lambda K` is `MvPolynomial ℕ K`, so `Λ_φ` is `MvPolynomial.mapAlgHom φ`. The plethystic
displacement takes values in polynomials in `w = z⁻¹` rather than Laurent polynomials in `z`, so
its coefficient extension is `Polynomial.mapAlgHom` of `Λ_φ`.

The slope operators divide by `M = (1 - q)(1 - u)`. Division is total and a homomorphism of fields
commutes with inversion (`map_inv₀`), so `lambdaMap_qop` holds without assuming admissibility of
`(q, u)`; at a non-admissible instance both sides are the totalised operators.
-/

@[expose] public section

namespace HJO.Ascent

open Finset HJO.Sym

section Transport

variable {K K' : Type*} [Field K] [Algebra ℚ K] [Field K'] [Algebra ℚ K']
variable (φ : K →ₐ[ℚ] K')

/-! ### The coefficient extension of the symmetric functions -/

/-- **The coefficient extension of the symmetric functions.** The ring homomorphism
`Λ_φ : Λ^K → Λ^{K'}` whose restriction to the coefficients is `φ` and which fixes every power sum
`p_k`. Since `Lambda K` is the polynomial ring on the power sums, that prescription is Mathlib's
coefficientwise map and no uniqueness argument is needed.

It is a homomorphism of `ℚ`-algebras, but not of `K'`-algebras: its source is not a `K'`-module.
Every statement below that calls a map linear says over which field. -/
@[hjo "def_asc_lambda_map"]
noncomputable def lambdaMap : Lambda K →ₐ[ℚ] Lambda K' := MvPolynomial.mapAlgHom φ

/-- The coefficient extension is the coefficientwise map. -/
theorem lambdaMap_apply (f : Lambda K) : lambdaMap φ f = MvPolynomial.map (φ : K →+* K') f := rfl

/-- The coefficient of a monomial in `Λ_φ f` is the image under `φ` of that coefficient of `f`. -/
@[simp]
theorem lambdaMap_coeff (f : Lambda K) (d : ℕ →₀ ℕ) :
    (lambdaMap φ f).coeff d = φ (f.coeff d) := by
  rw [lambdaMap_apply, MvPolynomial.coeff_map]
  rfl

/-- The coefficient extension carries a constant `a` to the constant `φ a`. -/
@[simp]
theorem lambdaMap_C (a : K) : lambdaMap φ (MvPolynomial.C a) = MvPolynomial.C (φ a) := by
  rw [lambdaMap_apply, MvPolynomial.map_C]
  rfl

/-- The coefficient extension fixes every generator. -/
@[simp]
theorem lambdaMap_X (i : ℕ) : lambdaMap φ (MvPolynomial.X i) = MvPolynomial.X i := by
  rw [lambdaMap_apply, MvPolynomial.map_X]

/-- The coefficient extension carries the monomial `a x^d` to `φ(a) x^d`. -/
@[simp]
theorem lambdaMap_monomial (d : ℕ →₀ ℕ) (a : K) :
    lambdaMap φ (MvPolynomial.monomial d a) = MvPolynomial.monomial d (φ a) := by
  rw [lambdaMap_apply, MvPolynomial.map_monomial]
  rfl

/-- The coefficient extension fixes every power sum, which is what pins it down. -/
@[simp]
theorem lambdaMap_powerSum (k : ℕ) : lambdaMap φ (powerSum K k) = powerSum K' k := by
  rw [powerSum, powerSum, lambdaMap_X]

/-- The coefficient extension carries a scalar multiple to the multiple by the image scalar. It is
`φ`-semilinear, not `K`-linear. -/
theorem lambdaMap_smul (a : K) (f : Lambda K) :
    lambdaMap φ (a • f) = φ a • lambdaMap φ f := by
  rw [← MvPolynomial.C_mul', ← MvPolynomial.C_mul', map_mul, lambdaMap_C]

/-! ### The coefficient extension of the Laurent polynomials -/

/-- **The coefficient extension of polynomials over the symmetric functions.** The map
`Λ^K[w] → Λ^{K'}[w]` acting on each coefficient by `Λ_φ`, where `w = z⁻¹`. -/
@[hjo "def_asc_laurent_map"]
noncomputable def laurentMap : Polynomial (Lambda K) →ₐ[ℚ] Polynomial (Lambda K') :=
  Polynomial.mapAlgHom (lambdaMap φ)

/-- The `j`-th coefficient of `laurentMap φ P` is `Λ_φ` of the `j`-th coefficient of `P`. -/
@[simp]
theorem laurentMap_coeff (P : Polynomial (Lambda K)) (j : ℕ) :
    (laurentMap φ P).coeff j = lambdaMap φ (P.coeff j) := by
  rw [laurentMap, Polynomial.coe_mapAlgHom, Polynomial.coeff_map]
  rfl

/-- The extension carries a constant polynomial `g` to the constant polynomial `Λ_φ g`. -/
@[simp]
theorem laurentMap_C (g : Lambda K) :
    laurentMap φ (Polynomial.C g) = Polynomial.C (lambdaMap φ g) := by
  rw [laurentMap, Polynomial.coe_mapAlgHom, Polynomial.map_C]
  rfl

/-- The extension fixes the variable. -/
@[simp]
theorem laurentMap_X : laurentMap φ (Polynomial.X : Polynomial (Lambda K)) = Polynomial.X := by
  rw [laurentMap, Polynomial.coe_mapAlgHom, Polynomial.map_X]

/-! ### The image spans, and the grading is preserved -/

/-- **The coefficient extension spans the larger ring.** `Λ^{K'}` is spanned as a `K'`-vector space
by the image of `Λ_φ`: the image contains every monomial in the power sums, and those span.

This is the base-change identification `Λ^{K'} = Λ^K ⊗_K K'` in the only form the ascent uses, and
it holds because `Lambda` is the polynomial ring on the power sums and for no other reason. It is
what turns an identity between operators over `K`, which asserts something about every element of
`Λ^K`, into one over `K'`: two `K'`-linear maps agreeing on a spanning set are equal. -/
@[hjo "lem_asc_lambda_map_spans"]
theorem span_range_lambdaMap :
    Submodule.span K' (Set.range (lambdaMap φ)) = ⊤ := by
  refine top_unique fun g _ => ?_
  rw [g.as_sum]
  refine Submodule.sum_mem _ fun d _ => ?_
  have hmon : MvPolynomial.monomial d (g.coeff d)
      = g.coeff d • MvPolynomial.monomial d (1 : K') := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hmon]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨MvPolynomial.monomial d (1 : K), ?_⟩)
  rw [lambdaMap_monomial, map_one]

/-- **The coefficient extension preserves the grading.** A symmetric function whose monomials all
have parts summing to `d` goes to one with the same property, the extension fixing every power sum
and `φ` being injective. -/
@[hjo "lem_asc_lambda_component"]
theorem lambdaMap_mem_lambdaComp {d : ℕ} {f : Lambda K} (hf : f ∈ LambdaComp K d) :
    lambdaMap φ f ∈ LambdaComp K' d := by
  rw [mem_lambdaComp] at hf ⊢
  intro e he
  refine hf fun h0 => he ?_
  rw [lambdaMap_coeff, h0, map_zero]

/-! ### Newton's two families -/

/-- **The coefficient extension fixes a complete homogeneous symmetric function.** Newton's
identity determines `h_n` from the power sums by rational scalars, and the extension fixes the
power sums and the rationals. -/
@[hjo "lem_asc_hsymm"]
theorem lambdaMap_completeHomog (n : ℕ) :
    lambdaMap φ (completeHomog K n) = completeHomog K' n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [UkRegular.completeHomog_zero, UkRegular.completeHomog_zero, map_one]
    | m + 1 =>
      rw [UkRegular.completeHomog_succ, UkRegular.completeHomog_succ, map_mul, lambdaMap_C,
        AlgHom.commutes, map_sum]
      refine congrArg _ (Finset.sum_congr rfl fun k hk => ?_)
      rw [mem_range] at hk
      rw [map_mul, lambdaMap_powerSum, ih (m - k) (by omega)]

/-- **The coefficient extension fixes an elementary symmetric function.** The same induction as for
the complete homogeneous ones, the scalars of Newton's identity being `(-1)^k / n`. -/
@[hjo "lem_asc_esymm"]
theorem lambdaMap_elemSymm (n : ℕ) :
    lambdaMap φ (elemSymm K n) = elemSymm K' n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [PhiE.elemSymm_zero, PhiE.elemSymm_zero, map_one]
    | m + 1 =>
      rw [PhiE.elemSymm_succ, PhiE.elemSymm_succ, map_mul, lambdaMap_C, AlgHom.commutes, map_sum]
      refine congrArg _ (Finset.sum_congr rfl fun k hk => ?_)
      rw [mem_range] at hk
      rw [map_mul, map_mul, map_pow, map_neg, map_one, lambdaMap_powerSum, ih (m - k) (by omega)]

/-! ### The plethystic displacement and the basic operators -/

/-- **The coefficient extension commutes with the plethystic displacement.** Both composites are
ring homomorphisms out of the polynomial ring on the power sums, so they need only be compared on
the coefficients, where each is `φ`, and on each generator, where the displaced coefficient
`(1 - q^k)(1 - u^k)` goes to `(1 - φ(q)^k)(1 - φ(u)^k)`. -/
@[hjo "lem_asc_pleth_shift"]
theorem laurentMap_plethShift (q u : K) (f : Lambda K) :
    laurentMap φ (plethShift q u f) = plethShift (φ q) (φ u) (lambdaMap φ f) := by
  have h : ((laurentMap φ).toRingHom.comp (plethShift q u).toRingHom :
      Lambda K →+* Polynomial (Lambda K')) =
      (plethShift (φ q) (φ u)).toRingHom.comp (lambdaMap φ).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · change laurentMap φ (plethShift q u (MvPolynomial.C a)) =
        plethShift (φ q) (φ u) (lambdaMap φ (MvPolynomial.C a))
      rw [plethShift_C, laurentMap_C, lambdaMap_C, plethShift_C]
    · change laurentMap φ (plethShift q u (MvPolynomial.X i)) =
        plethShift (φ q) (φ u) (lambdaMap φ (MvPolynomial.X i))
      rw [plethShift_gen, lambdaMap_X, plethShift_gen, map_add, map_mul, map_pow, laurentMap_C,
        laurentMap_C, laurentMap_X, lambdaMap_X, lambdaMap_C, map_mul, map_sub, map_sub, map_one,
        map_pow, map_pow]
  exact RingHom.congr_fun h f

/-- The pairing against a family of symmetric functions transports: the extension of the pairing is
the pairing of the extended family against the extended Laurent polynomial. -/
theorem lambdaMap_coeffPairing (c : ℕ → Lambda K) (P : Polynomial (Lambda K)) :
    lambdaMap φ (coeffPairing c P) =
      coeffPairing (fun j => lambdaMap φ (c j)) (laurentMap φ P) := by
  have hP : ∀ j : ℕ, P.natDegree + 1 ≤ j → P.coeff j = 0 := fun j hj =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hQ : ∀ j : ℕ, P.natDegree + 1 ≤ j → (laurentMap φ P).coeff j = 0 := fun j hj => by
    rw [laurentMap_coeff, hP j hj, map_zero]
  rw [coeffPairing_eq_sum_range c P hP, coeffPairing_eq_sum_range _ _ hQ, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_mul, laurentMap_coeff]

/-- **The coefficient extension intertwines the basic operators.** The displacement transports, the
elementary symmetric functions are fixed, and the pairing that reads off the coefficient of `z^k`
transports with them. -/
@[hjo "lem_asc_dop"]
theorem lambdaMap_dop (q u : K) (k : ℕ) (f : Lambda K) :
    lambdaMap φ (Dop q u k f) = Dop (φ q) (φ u) k (lambdaMap φ f) := by
  rw [dop_apply, dop_apply, lambdaMap_coeffPairing, laurentMap_plethShift]
  refine congrArg (fun c => coeffPairing c _) (funext fun j => ?_)
  rw [map_mul, map_pow, map_neg, map_one, lambdaMap_elemSymm]

/-! ### The slope operators -/

/-- The scalar the slope operators divide by transports, a homomorphism of fields commuting with
inversion. This is the whole of what the recursion needs of `φ`, and it is why the transport of the
slope operators asks nothing of the parameters. -/
theorem map_mparam_inv (q u : K) :
    φ (((1 - q) * (1 - u))⁻¹) = ((1 - φ q) * (1 - φ u))⁻¹ := by
  rw [map_inv₀, map_mul, map_sub, map_sub, map_one]

/-- The fuelled recursion of the slope operators transports at every amount of fuel and every
slope. -/
theorem lambdaMap_qopAux (q u : K) :
    ∀ (fuel m n : ℕ) (f : Lambda K),
      lambdaMap φ (QopAux q u fuel m n f) = QopAux (φ q) (φ u) fuel m n (lambdaMap φ f) := by
  intro fuel
  induction fuel with
  | zero => intro m n f; rw [qopAux_zero, qopAux_zero, lambdaMap_dop]
  | succ fuel ih =>
    intro m n f
    rw [qopAux_succ_def, qopAux_succ_def]
    split_ifs with hm
    · rw [lambdaMap_dop]
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, lambdaMap_smul, map_mparam_inv,
        LinearMap.sub_apply, LinearMap.sub_apply, map_sub, Module.End.mul_apply,
        Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, ih, ih, ih, ih]

/-- The primitive evaluator of the slope operators transports. -/
theorem lambdaMap_qopPrim (q u : K) (m n : ℕ) (f : Lambda K) :
    lambdaMap φ (QopPrim q u m n f) = QopPrim (φ q) (φ u) m n (lambdaMap φ f) :=
  lambdaMap_qopAux φ q u m m n f

/-- **The coefficient extension intertwines the slope operators.** The split of a slope and the
fuel of the recursion are functions of natural numbers, so they are the same at both instances, and
the only scalar the recursion forms is `M⁻¹`, which transports by `map_mparam_inv`. -/
@[hjo "lem_asc_qop"]
theorem lambdaMap_qop (q u : K) (m n : ℕ) (f : Lambda K) :
    lambdaMap φ (Qop q u m n f) = Qop (φ q) (φ u) m n (lambdaMap φ f) := by
  rw [Qop, Qop]
  split_ifs with hm hc
  · rw [lambdaMap_dop]
  · rw [lambdaMap_qopPrim]
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, lambdaMap_smul, map_mparam_inv,
      LinearMap.sub_apply, LinearMap.sub_apply, map_sub, Module.End.mul_apply,
      Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, lambdaMap_qopPrim,
      lambdaMap_qopPrim, lambdaMap_qopPrim, lambdaMap_qopPrim]

/-! ### A commuting pair ascends -/

/-- **A commuting pair ascends.** Two `K'`-linear endomorphisms of `Λ^{K'}` that are intertwined
with a commuting pair of `K`-linear endomorphisms of `Λ^K` along the coefficient extension commute.
They agree on the image of the extension, the set where two `K'`-linear maps agree is a
`K'`-subspace, and that image spans. -/
@[hjo "lem_asc_operator_commute"]
theorem commute_of_intertwined {A B : Module.End K (Lambda K)} {A' B' : Module.End K' (Lambda K')}
    (hA : ∀ f : Lambda K, lambdaMap φ (A f) = A' (lambdaMap φ f))
    (hB : ∀ f : Lambda K, lambdaMap φ (B f) = B' (lambdaMap φ f))
    (hAB : Commute A B) : Commute A' B' := by
  have hspan : Submodule.span K' (Set.range (lambdaMap φ)) = ⊤ := span_range_lambdaMap φ
  refine LinearMap.ext fun g => ?_
  have hmem : g ∈ Submodule.span K' (Set.range (lambdaMap φ)) := by rw [hspan]; trivial
  refine Submodule.span_induction (p := fun g _ => (A' * B') g = (B' * A') g) ?_ ?_ ?_ ?_ hmem
  · rintro _ ⟨f, rfl⟩
    rw [Module.End.mul_apply, Module.End.mul_apply, ← hB, ← hA, ← hA, ← hB,
      ← Module.End.mul_apply, ← Module.End.mul_apply, hAB.eq]
  · simp
  · intro x y _ _ hx hy
    simp only [Module.End.mul_apply, map_add] at hx hy ⊢
    rw [hx, hy]
  · intro a x _ hx
    simp only [Module.End.mul_apply, map_smul] at hx ⊢
    rw [hx]

/-- **The slope operators at the image parameters commute when they commute at the source.** If
`Q_{m,n}` and `Q_{m',n'}` commute at `(q, u)`, they commute at `(φ q, φ u)`. -/
theorem commute_qop_map {q u : K} {m n m' n' : ℕ}
    (h : Commute (Qop q u m n) (Qop q u m' n')) :
    Commute (Qop (φ q) (φ u) m n) (Qop (φ q) (φ u) m' n') :=
  commute_of_intertwined φ (lambdaMap_qop φ q u m n) (lambdaMap_qop φ q u m' n') h

end Transport

end HJO.Ascent
