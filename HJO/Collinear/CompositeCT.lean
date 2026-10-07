/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.ExpShift
public import HJO.Collinear.ShiftIterate
public import HJO.Collinear.ScalarFamily
public import HJO.Collinear.SSSPairing
public meta import HJO.Attr

/-! # A composite of basic operators is a constant term

BGLX's Proposition 1.2 writes a composite of the basic operators of
`HJO/Symmetric/SymmetricFunctions.lean` as a single constant term in `k` variables,

`D_{a_k} ∘ ⋯ ∘ D_{a_1}(F) = CT_k(δ^{(k)}(F) E_k z^{-a} Ω̂_k)`,

the product of the four factors being formed in the cone ring `R^{id}_k` of
`HJO/Collinear/ConeRing.lean`. This file forms that product — `compositeElem` — and proves the
formula, which is the bridge between the operator side of BGLX's criterion and the Laurent-series
side their Theorem 2.1 computes with.

The proof is the induction on the number of variables. Each step peels off the last
variable: the four factors in `k+1` variables are the displacement `δ̃_{k+1}` of
`HJO/Collinear/ConeGraded.lean` applied to the four factors in `k` variables, times the two
factors `E^{(k)} z_{k+1}^{-a_k}` living on the last variable alone. That is `compositeElem_succ`,
and it is assembled from the four one-factor computations already available: `δ̃_{k+1}` turns
`δ^{(k)}(F)` into `δ^{(k+1)}(F)` (`shiftExtendElem_plethShiftMulti`), turns `E_k` into its padding
times the `k` new rays of the kernel (`shiftExtendElem_expAlphabet`), and is the padding on the
monomial and on the kernel expansion, whose coefficients are scalars. What is left over on each side
matches after `ring`.

The constant term of that product is then the last operator applied to the constant term in `k`
variables — `ct_shiftExtendElem_mul`, the computation behind the two displays of BGLX's proof.
Only the exponents on the ray of the last variable contribute, and the finite range they run over is
cut out by the degree of `δ(G)`: below `z_{k+1}^0` the displaced family vanishes, and above the
degree of `δ(G)` its coefficients do.

## Main definitions

* `HJO.Bglx.compositeElem`: the product `δ^{(k)}(F) E_k z^{-a} Ω̂_k` in `R^{id}_k`.

## Main statements

* `HJO.Bglx.isDegreeControlled_compositeElem`: the product is degree-controlled, so the displacement
  in the last variable may be applied to it.
* `HJO.Bglx.compositeElem_succ`: the four factors split off their last variable.
* `HJO.Bglx.ct_shiftExtendElem_mul`: taking the constant term of a displaced family against the two
  factors of the last variable applies one basic operator.
* `HJO.Bglx.dopComp_eq_ct`: **BGLX's composite formula.**

## Implementation notes

**The degree-control argument of `shiftExtendElem` is proof-irrelevant but appears in the type of
the element.** Rewriting the element inside it does not typecheck, so
`shiftExtendElem_compositeElem` supplies the unfolded product together with a proof stated for that
product and moves to it by `show`; from there the multiplicativity of the displacement is applied
with the *named* proofs the four one-factor lemmas carry, which is what lets `rw` fire on them.

**The window of exponents is `b + (D + 1)`, split at `b`.** The contributing exponents of the
convolution at `0` are the `z_{k+1}^{b-r}` with `r < b + D + 1`, `D` being the degree of `δ(G)`; the
block `r < b` contributes nothing because the displaced family has no positive power of `z_{k+1}`,
and the block `r = b + j` reproduces exactly the finite sum that `dop_apply_eq_sum_range` writes
the basic operator as.

## References

F. Bergeron, A. M. Garsia, E. Leven and G. Xin, *Some remarkable new plethystic operators in the
theory of Macdonald polynomials*, arXiv:1405.0316v1, J. Comb. **7** (2016) 671--714, Proposition
1.2, equation (1.17), formalised as `HJO.Bglx.dopComp_eq_ct`, with Definitions `HJO.Sym.DopInt`,
`HJO.Bglx.ct`, `HJO.Bglx.plethShiftMulti`, `HJO.Bglx.expAlphabet`, `HJO.Bglx.kernelExpansion` and
`HJO.Bglx.shiftExtend`.
-/

@[expose] public section

namespace HJO.Bglx

open HJO.Sym

variable {K : Type*} [CommRing K] [Algebra ℚ K] {k : ℕ}

/-- The basic operator as a finite sum over the coefficients of the displacement: past the degree
of `δ f` the terms vanish, so any strict bound on that degree is a range to sum over. -/
theorem dop_apply_eq_sum_range (q u : K) (b : ℕ) (f : Lambda K) {N : ℕ}
    (hN : (plethShift q u f).natDegree < N) :
    Dop q u b f = ∑ j ∈ Finset.range N,
      Polynomial.coeff (plethShift q u f) j * ((-1) ^ (b + j) * elemSymm K (b + j)) := by
  rw [Dop, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  exact Polynomial.sum_over_range'
    (f := fun (j : ℕ) (A : Lambda K) => A * ((-1) ^ (b + j) * elemSymm K (b + j)))
    _ (fun j => zero_mul _) N hN

/-- At no variables the constant term is multiplicative, the cone ring in `0` variables being the
coefficient ring itself. -/
lemma ct_mul_zero_vars {R : Type*} [CommRing R] (τ : Equiv.Perm (Fin 0)) (x y : ConeRing 0 τ R) :
    ct 0 R (x * y).coeff = ct 0 R x.coeff * ct 0 R y.coeff := by
  have h := map_mul (ConeRing.zeroVarsAlgEquiv (R := R) τ) x y
  simpa [ConeRing.zeroVarsAlgEquiv] using h

/-- **The product of the four factors of BGLX's composite formula**,
`δ^{(k)}(F) E_k z^{-a} Ω̂_k`, formed in the cone ring of the identity ordering. -/
noncomputable def compositeElem (q u : K) (k : ℕ) (a : Fin k → ℕ) (F : Lambda K) :
    ConeRing k 1 (Lambda K) :=
  shiftExpElem q u k 1 F * (monoElem 1 (negExp a) * kernelExpansion q u k)

/-- **The four factors are degree-controlled**, so the displacement in the last variable applies to
their product: the first and third have finite support, the second has the bound `N = 0` and the
fourth is a balanced family of scalars. -/
theorem isDegreeControlled_compositeElem (q u : K) (k : ℕ) (a : Fin k → ℕ) (F : Lambda K) :
    IsDegreeControlled (compositeElem q u k a F).coeff := by
  rw [compositeElem, shiftExpElem]
  exact isDegreeControlled_mul
    (isDegreeControlled_mul (isDegreeControlled_laurentToCone _)
      (isDegreeControlled_expAlphabet K k))
    (isDegreeControlled_mul (isDegreeControlled_monoElem _)
      (isDegreeControlled_of_isBalancedScalar (isBalancedScalar_kernelExpansion q u k)))

/-- **The composite formula at no variables**: the composite is empty, every factor but `δ^{(0)}(F)`
is `1`, and `CT_0` reads off `F`. -/
theorem dopComp_eq_ct_zero (q u : K) (a : Fin 0 → ℕ) (F : Lambda K) :
    (List.ofFn fun i => Dop q u (a i)).reverse.prod F
      = ct 0 (Lambda K) (compositeElem q u 0 a F).coeff := by
  have hzero : negExp a = 0 := Finsupp.ext fun i => i.elim0
  have hker : kernelExpansion q u 0 = 1 := by rw [kernelExpansion]; simp
  have hexp : ∀ α : Fin 0 →₀ ℤ, (expAlphabet K 0 1).coeff α = 1 := fun α => by
    rw [coeff_expAlphabet]; simp
  rw [compositeElem, shiftExpElem, hker, mul_one, ct_mul_zero_vars, ct_mul_zero_vars, hzero]
  rw [ct_apply, ct_apply, ct_apply, coeff_laurentToCone, hexp, coeff_monoElem,
    plethShiftMulti_zero_vars]
  simp

/-- The exponent `-a` splits off its last coordinate. -/
lemma negExp_succ (a : Fin (k + 1) → ℕ) :
    negExp a = snocExp (negExp fun i => a i.castSucc) (-(a (Fin.last k) : ℤ)) := by
  refine Finsupp.ext fun i => ?_
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [negExp_apply, snocExp_castSucc, negExp_apply]
  · rw [negExp_apply, snocExp_last]

/-- **The displacement in the last variable of the four factors**, computed factor by factor. -/
theorem shiftExtendElem_compositeElem (q u : K) (k : ℕ) (a : Fin k → ℕ) (F : Lambda K)
    (h : IsDegreeControlled (compositeElem q u k a F).coeff) :
    shiftExtendElem q u (compositeElem q u k a F) h
      = laurentToCone 1 (plethShiftMulti q u (k + 1) F)
          * (padElem (expAlphabet K k 1)
            * ∏ i : Fin k, kernelRay q u (Fin.castSucc_lt_last i))
          * (padElem (monoElem 1 (negExp a)) * padElem (kernelExpansion q u k)) := by
  have hmul : ∀ (x y : ConeRing k 1 (Lambda K)) (hx : IsDegreeControlled x.coeff)
      (hy : IsDegreeControlled y.coeff) (hxy : IsDegreeControlled (x * y).coeff),
      shiftExtendElem q u (x * y) hxy = shiftExtendElem q u x hx * shiftExtendElem q u y hy :=
    fun x y hx hy _ => shiftExtendElem_mul q u x y hx hy
  have h' : IsDegreeControlled (laurentToCone 1 (plethShiftMulti q u k F) * expAlphabet K k 1
      * (monoElem 1 (negExp a) * kernelExpansion q u k) : ConeRing k 1 (Lambda K)).coeff :=
    isDegreeControlled_mul
      (isDegreeControlled_mul (isDegreeControlled_laurentToCone _)
        (isDegreeControlled_expAlphabet K k))
      (isDegreeControlled_mul (isDegreeControlled_monoElem _)
        (isDegreeControlled_of_isBalancedScalar (isBalancedScalar_kernelExpansion q u k)))
  change shiftExtendElem q u
      (laurentToCone 1 (plethShiftMulti q u k F) * expAlphabet K k 1
        * (monoElem 1 (negExp a) * kernelExpansion q u k)) h' = _
  rw [hmul _ _ (isDegreeControlled_mul (isDegreeControlled_laurentToCone _)
      (isDegreeControlled_expAlphabet K k))
    (isDegreeControlled_mul (isDegreeControlled_monoElem _)
      (isDegreeControlled_of_isBalancedScalar (isBalancedScalar_kernelExpansion q u k))),
    hmul _ _ (isDegreeControlled_laurentToCone _) (isDegreeControlled_expAlphabet K k),
    hmul _ _ (isDegreeControlled_monoElem _)
      (isDegreeControlled_of_isBalancedScalar (isBalancedScalar_kernelExpansion q u k)),
    shiftExtendElem_plethShiftMulti, shiftExtendElem_expAlphabet, shiftExtendElem_monoElem,
    shiftExtendElem_of_isBalancedScalar q u _ (isBalancedScalar_kernelExpansion q u k)]

/-- **The four factors split off their last variable.** -/
theorem compositeElem_succ (q u : K) (k : ℕ) (a : Fin (k + 1) → ℕ) (F : Lambda K) :
    compositeElem q u (k + 1) a F
      = shiftExtendElem q u (compositeElem q u k (fun i => a i.castSucc) F)
            (isDegreeControlled_compositeElem q u k _ F)
          * (expRay K 1 (Fin.last k)
            * monoElem 1 (Finsupp.single (Fin.last k) (-(a (Fin.last k) : ℤ)))) := by
  rw [shiftExtendElem_compositeElem, compositeElem, shiftExpElem, expAlphabet_succ, negExp_succ,
    monoElem_snocExp, kernelExpansion_succ]
  ring

/-- The coefficients of the last two factors, `E^{(k)} z_{k+1}^{-b}`: the monomial shifts the
exponent of the exponential ray of the last variable. -/
lemma coeff_expRay_mul_monoElem (b : ℕ) (γ : Fin (k + 1) →₀ ℤ) :
    (expRay K 1 (Fin.last k)
        * monoElem 1 (Finsupp.single (Fin.last k) (-(b : ℤ)))).coeff γ
      = (expRay K 1 (Fin.last k)).coeff (γ + Finsupp.single (Fin.last k) (b : ℤ)) := by
  rw [mul_comm, congrFun (coeff_monoElem_mul (Finsupp.single (Fin.last k) (-(b : ℤ)))
    (expRay K 1 (Fin.last k))) γ, monoMul_apply, Finsupp.single_neg, sub_neg_eq_add]

/-- The coefficient of the last two factors on the ray of the last variable. -/
lemma coeff_expRay_mul_monoElem_single (b r : ℕ) :
    (expRay K 1 (Fin.last k)
        * monoElem 1 (Finsupp.single (Fin.last k) (-(b : ℤ)))).coeff
        (Finsupp.single (Fin.last k) ((r : ℤ) - b))
      = (-1) ^ r * elemSymm K r := by
  rw [coeff_expRay_mul_monoElem, ← Finsupp.single_add,
    show (r : ℤ) - b + b = (r : ℤ) from by ring, coeff_expRay_natCast]

/-- An exponent carrying a nonzero coefficient of the last two factors lies on the ray of the last
variable, at an exponent `r - b` with `r` a natural number. -/
lemma exists_of_coeff_expRay_mul_monoElem_ne_zero (b : ℕ) {γ : Fin (k + 1) →₀ ℤ}
    (h : (expRay K 1 (Fin.last k)
      * monoElem 1 (Finsupp.single (Fin.last k) (-(b : ℤ)))).coeff γ ≠ 0) :
    ∃ r : ℕ, γ = Finsupp.single (Fin.last k) ((r : ℤ) - b) := by
  rw [coeff_expRay_mul_monoElem] at h
  obtain ⟨r, hr⟩ := exists_natCast_of_coeff_expRay_ne_zero _ h
  refine ⟨r, ?_⟩
  have hγ : γ = Finsupp.single (Fin.last k) (r : ℤ) - Finsupp.single (Fin.last k) (b : ℤ) := by
    rw [← hr]; abel
  rw [hγ, ← Finsupp.single_sub]

omit [Algebra ℚ K] in
/-- The coefficient of the displaced family on the ray of the last variable, at a nonpositive
exponent: the constant term of the family is displaced and its `w`-coefficient read off. -/
lemma coeff_shiftExtendElem_single_last (q u : K) (W : ConeRing k 1 (Lambda K))
    (hW : IsDegreeControlled W.coeff) {c : ℤ} (hc : c ≤ 0) :
    (shiftExtendElem q u W hW).coeff (Finsupp.single (Fin.last k) c)
      = Polynomial.coeff (plethShift q u (ct k (Lambda K) W.coeff)) (-c).toNat := by
  rw [coeff_shiftExtendElem, ← snocExp_zero_last c, shiftExtend_snocExp q u _ _ hc, ct_apply]

omit [Algebra ℚ K] in
/-- No positive power of the last variable occurs in the displaced family. -/
lemma coeff_shiftExtendElem_single_last_of_pos (q u : K) (W : ConeRing k 1 (Lambda K))
    (hW : IsDegreeControlled W.coeff) {c : ℤ} (hc : 0 < c) :
    (shiftExtendElem q u W hW).coeff (Finsupp.single (Fin.last k) c) = 0 := by
  rw [coeff_shiftExtendElem, ← snocExp_zero_last c, shiftExtend_snocExp_of_pos q u _ _ hc]

/-- **The constant-term step of the induction**: the constant term in `k+1` variables of the
displaced family times the last two factors is the basic operator `D_b` applied to the constant term
in `k` variables. -/
theorem ct_shiftExtendElem_mul (q u : K) (k : ℕ) (b : ℕ) (W : ConeRing k 1 (Lambda K))
    (hW : IsDegreeControlled W.coeff) :
    ct (k + 1) (Lambda K)
        (shiftExtendElem q u W hW
          * (expRay K 1 (Fin.last k)
            * monoElem 1 (Finsupp.single (Fin.last k) (-(b : ℤ))))).coeff
      = Dop q u b (ct k (Lambda K) W.coeff) := by
  classical
  set G : Lambda K := ct k (Lambda K) W.coeff with hG
  set D : ℕ := (plethShift q u G).natDegree with hD
  set S : Finset (Fin (k + 1) →₀ ℤ) := (Finset.range (b + (D + 1))).image
    fun r : ℕ => Finsupp.single (Fin.last k) ((b : ℤ) - r) with hS
  have hsub : ConeRing.convSupport (shiftExtendElem q u W hW)
      (expRay K 1 (Fin.last k) * monoElem 1 (Finsupp.single (Fin.last k) (-(b : ℤ))))
      0 ⊆ ↑S := by
    rintro γ' ⟨h1, h2⟩
    obtain ⟨r, hr⟩ := exists_of_coeff_expRay_mul_monoElem_ne_zero b h2
    have hγ' : γ' = Finsupp.single (Fin.last k) ((b : ℤ) - r) := by
      have hneg : γ' = -Finsupp.single (Fin.last k) ((r : ℤ) - b) := by rw [← hr]; abel
      rw [hneg, ← Finsupp.single_neg, neg_sub]
    have hle : (b : ℤ) - r ≤ 0 := by
      by_contra hc
      exact h1 (by rw [hγ', coeff_shiftExtendElem_single_last_of_pos q u W hW (by omega)])
    rw [hγ', coeff_shiftExtendElem_single_last q u W hW hle,
      show (-((b : ℤ) - r)).toNat = r - b from by omega, ← hG] at h1
    have hrb : r - b ≤ D := by
      by_contra hc
      exact h1 (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
    rw [hS, Finset.mem_coe, Finset.mem_image]
    exact ⟨r, Finset.mem_range.2 (by omega), hγ'.symm⟩
  have hinj : ∀ r ∈ Finset.range (b + (D + 1)), ∀ r' ∈ Finset.range (b + (D + 1)),
      (Finsupp.single (Fin.last k) ((b : ℤ) - r) : Fin (k + 1) →₀ ℤ)
        = Finsupp.single (Fin.last k) ((b : ℤ) - r') → r = r' := by
    intro r _ r' _ hrr
    have h' := congrArg (fun f : Fin (k + 1) →₀ ℤ => f (Fin.last k)) hrr
    simp only [Finsupp.single_eq_same] at h'
    omega
  have hterm : ∀ r : ℕ, (shiftExtendElem q u W hW).coeff (Finsupp.single (Fin.last k)
        ((b : ℤ) - r))
      * (expRay K 1 (Fin.last k)
          * monoElem 1 (Finsupp.single (Fin.last k) (-(b : ℤ)))).coeff
          (0 - Finsupp.single (Fin.last k) ((b : ℤ) - r))
      = (shiftExtendElem q u W hW).coeff (Finsupp.single (Fin.last k) ((b : ℤ) - r))
        * ((-1) ^ r * elemSymm K r) := by
    intro r
    rw [show (0 : Fin (k + 1) →₀ ℤ) - Finsupp.single (Fin.last k) ((b : ℤ) - r)
        = Finsupp.single (Fin.last k) ((r : ℤ) - b) from by
      rw [zero_sub, ← Finsupp.single_neg, neg_sub], coeff_expRay_mul_monoElem_single]
  have hzero : ∀ r ∈ Finset.range (b + (D + 1)), r ∉ Finset.Ico b (b + (D + 1)) →
      (shiftExtendElem q u W hW).coeff (Finsupp.single (Fin.last k) ((b : ℤ) - r))
        * ((-1) ^ r * elemSymm K r) = 0 := by
    intro r hr hr2
    rw [Finset.mem_range] at hr
    have hrb : r < b := by
      by_contra hc
      exact hr2 (Finset.mem_Ico.2 ⟨by omega, hr⟩)
    rw [coeff_shiftExtendElem_single_last_of_pos q u W hW
      (by omega : (0 : ℤ) < (b : ℤ) - r), zero_mul]
  have hIco : Finset.Ico b (b + (D + 1)) ⊆ Finset.range (b + (D + 1)) :=
    fun r hr => Finset.mem_range.2 (Finset.mem_Ico.1 hr).2
  rw [ct_apply, ConeRing.coeff_mul_of_subset _ _ _ _ hsub, hS, Finset.sum_image hinj,
    Finset.sum_congr rfl fun r _ => hterm r, ← Finset.sum_subset hIco hzero,
    Finset.sum_Ico_eq_sum_range, show b + (D + 1) - b = D + 1 from by omega,
    dop_apply_eq_sum_range q u b G (N := D + 1) (by rw [hD]; omega)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_shiftExtendElem_single_last q u W hW
      (by push_cast; omega : (b : ℤ) - ((b + j : ℕ) : ℤ) ≤ 0),
    show (-((b : ℤ) - ((b + j : ℕ) : ℤ))).toNat = j from by push_cast; omega, ← hG]

/-- The composite of `k+1` basic operators is the last one applied to the composite of the first
`k`: the word's last index sits at the head of the reversed list. -/
lemma dopComp_succ (q u : K) (k : ℕ) (a : Fin (k + 1) → ℕ) (F : Lambda K) :
    (List.ofFn fun i => Dop q u (a i)).reverse.prod F
      = Dop q u (a (Fin.last k)) ((List.ofFn fun i => Dop q u (a i.castSucc)).reverse.prod F) := by
  rw [List.ofFn_succ_last, List.reverse_concat, List.prod_cons, Module.End.mul_apply]

/-- **BGLX's composite formula.** A composite of basic operators is the constant term of the
product of the four factors: `D_{a_k} ∘ ⋯ ∘ D_{a_1}(F) = CT_k(δ^{(k)}(F) E_k z^{-a} Ω̂_k)`. -/
@[hjo "lem_bglx_composite_ct"]
theorem dopComp_eq_ct (q u : K) (k : ℕ) (a : Fin k → ℕ) (F : Lambda K) :
    (List.ofFn fun i => Dop q u (a i)).reverse.prod F
      = ct k (Lambda K) (compositeElem q u k a F).coeff := by
  induction k with
  | zero => exact dopComp_eq_ct_zero q u a F
  | succ k ih =>
    rw [dopComp_succ, ih fun i => a i.castSucc, compositeElem_succ, ct_shiftExtendElem_mul]

end HJO.Bglx
