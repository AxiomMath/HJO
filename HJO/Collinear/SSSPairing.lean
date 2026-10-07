/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.PlethShiftMulti
public meta import HJO.Attr

/-! # The Stanton--Stembridge pairing for the BGLX composite

The criterion of BGLX pairs an operator against the *symmetrised* symbol, and the step that lets the
symmetrisation be moved from one factor to the other is the Stanton--Stembridge trick in the form
their proof of Theorem 2.1 actually uses: for every permutation `τ` of the variables,

`CT_k(δ^{(k)}(F) E_k g) = CT_k(δ^{(k)}(F) E_k τ_*g)`,

the product on the left formed in `R^id_k` and the one on the right in `R^τ_k`. What makes it work
is that the first two factors are *symmetric*: the displacement in `k` variables sends `p_j` to
`p_j + κ(p_j)(z_1^{-j} + ⋯ + z_k^{-j})`, a symmetric Laurent polynomial, and the exponential factor
`E_k` has a coefficient depending only on the multiset of coordinates. Constant-term extraction is
invariant under relabelling because a permutation fixes the zero exponent.

This is not a consequence of the Laurent-polynomial Stanton--Stembridge lemma over `𝕜` and does not
imply it: the coefficients here lie in `Λ` rather than in `𝕜` and the factor being symmetrised is an
infinite formal sum. The proof needs the relabelling isomorphisms between the `k!` cone rings, which
is also why the symmetrisation in BGLX lands in the module of *all* formal sums and in no one
of those rings.

## Main definitions

* `HJO.Bglx.shiftExpElem`: the product `δ^{(k)}(F) E_k`, in the cone ring of an ordering.

## Main statements

* `HJO.Bglx.coeff_shiftExpElem_congr`: its coefficient family does not depend on the ordering.
* `HJO.Bglx.relabel_coeff_shiftExpElem`: it is symmetric in the variables.
* `HJO.Bglx.ct_mul_eq_ct_mul_relabel`: the pairing itself.

## Implementation notes

**Where the relabelled factor is quantified rather than constructed.** `τ_*g` for
`g ∈ R^{id}_k` is a member of `R^τ_k`, and Lean's `ConeRing k τ` and `ConeRing k (τ * 1)` are
different types even though the permutations are equal. Rather than transporting along that
equality, `ct_mul_eq_ct_mul_relabel` quantifies over the element `g'` of `R^τ_k` *together with*
the hypothesis that its coefficient family is `τ_*` of `g`'s — which is exactly what "let `τ_*g` be
formed in `R^τ_k`" means, and leaves nothing to a cast.
`HJO.Bglx.ConeRing.relabelAlgEquiv` supplies such a `g'` whenever one is wanted.

**The symmetry is proved on the two factors separately**: `relabel` is
multiplicative on the cone rings (`HJO.Bglx.ConeRing.coeff_relabelAlgEquiv` with `map_mul`), the
displacement is fixed by `HJO.Bglx.relabel_coeff_plethShiftMulti` and the exponential factor by
`HJO.Bglx.relabel_coeff_expAlphabet`.

## References

The reference for the lemmas `HJO.Bglx.relabel_coeff_shiftExpElem` and
`HJO.Bglx.ct_mul_eq_ct_mul_relabel` is F. Bergeron, A. M. Garsia, E. Leven and G.
Xin, *Some remarkable new plethystic operators in the theory of Macdonald polynomials*,
arXiv:1405.0316v1, J. Comb. **7** (2016) 671--714; the pairing is the case their remark after
equation (2.7) asserts without proof, and the trick is D. Stanton and J. Stembridge's.
-/

@[expose] public section

namespace HJO.Bglx

open HJO.Sym

variable {K : Type*} [CommRing K] [Algebra ℚ K] {k : ℕ}

/-- The product `δ^{(k)}(F) E_k` of the displaced symmetric function with the exponential factor,
formed in the cone ring of the ordering `τ`. -/
noncomputable def shiftExpElem (q u : K) (k : ℕ) (τ : Equiv.Perm (Fin k)) (F : Lambda K) :
    ConeRing k τ (Lambda K) :=
  laurentToCone τ (plethShiftMulti q u k F) * expAlphabet K k τ

/-- **The coefficients of `δ^{(k)}(F) E_k` do not depend on the ordering.** Both factors have
ordering-independent coefficients and the product is the same convolution in every cone ring, so the
element may be formed in whichever `R^τ_k` a statement needs. -/
theorem coeff_shiftExpElem_congr (q u : K) (k : ℕ) (σ τ : Equiv.Perm (Fin k)) (F : Lambda K) :
    (shiftExpElem q u k σ F).coeff = (shiftExpElem q u k τ F).coeff := by
  refine ConeRing.coeff_mul_congr _ _ _ _ ?_ ?_
  · funext α
    rw [coeff_laurentToCone, coeff_laurentToCone]
  · funext α
    rw [coeff_expAlphabet, coeff_expAlphabet]

/-- **The displaced exponential factor is symmetric.** Relabelling the variables fixes
`δ^{(k)}(F) E_k`: the displacement is a symmetric Laurent polynomial and the coefficient of the
exponential factor depends only on the multiset of coordinates. -/
@[hjo "lem_bglx_shift_exp_symmetric"]
theorem relabel_coeff_shiftExpElem (q u : K) (k : ℕ) (σ : Equiv.Perm (Fin k)) (F : Lambda K) :
    relabel σ (shiftExpElem q u k 1 F).coeff = (shiftExpElem q u k 1 F).coeff := by
  have hmul := ConeRing.coeff_relabelAlgEquiv σ 1
    (laurentToCone (1 : Equiv.Perm (Fin k)) (plethShiftMulti q u k F) * expAlphabet K k 1)
  rw [shiftExpElem]
  funext α
  rw [← hmul α, map_mul]
  refine congrFun (ConeRing.coeff_mul_congr _ _ _ _ ?_ ?_) α
  · funext β
    rw [ConeRing.coeff_relabelAlgEquiv, coeff_laurentToCone]
    exact congrFun (relabel_coeff_plethShiftMulti q u k σ F) β
  · funext β
    rw [ConeRing.coeff_relabelAlgEquiv]
    exact congrFun (relabel_coeff_expAlphabet σ) β

/-- **Symmetrising the second factor does not change the constant term.** For every permutation `τ`
of the variables, the constant term of `δ^{(k)}(F) E_k g` formed in `R^{id}_k` is the constant term
of `δ^{(k)}(F) E_k τ_*g` formed in `R^τ_k`. The relabelled factor is quantified as `g'` with its
defining property, which is what "the product on the right formed in `R^τ_k`" means. -/
@[hjo "lem_bglx_sss_pairing"]
theorem ct_mul_eq_ct_mul_relabel (q u : K) {k : ℕ} (F : Lambda K) (τ : Equiv.Perm (Fin k))
    (g : ConeRing k 1 (Lambda K)) (g' : ConeRing k τ (Lambda K))
    (hg' : g'.coeff = relabel τ g.coeff) :
    ct k (Lambda K) (shiftExpElem q u k 1 F * g).coeff
      = ct k (Lambda K) (shiftExpElem q u k τ F * g').coeff := by
  have hrel := ConeRing.coeff_relabelAlgEquiv τ 1 (shiftExpElem q u k 1 F * g)
  have hkey : relabel τ (shiftExpElem q u k 1 F * g).coeff
      = (shiftExpElem q u k τ F * g').coeff := by
    funext α
    rw [← hrel α, map_mul]
    refine congrFun (ConeRing.coeff_mul_congr _ _ _ _ ?_ ?_) α
    · funext β
      rw [ConeRing.coeff_relabelAlgEquiv]
      exact congrFun ((relabel_coeff_shiftExpElem q u k τ F).trans
        (coeff_shiftExpElem_congr q u k 1 τ F)) β
    · funext β
      rw [ConeRing.coeff_relabelAlgEquiv, hg']
  rw [← hkey, ct_relabel]

end HJO.Bglx
