/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.Bop
public import HJO.CarlssonMellit.SweepCM
public import HJO.Shuffle.MellitShiftGenerators
public meta import HJO.Attr

/-! # The Hall--Littlewood operators on the sweep module, and the lowering operator on `y_kⁱ F`

The family `B_r` of `HJO.Sym.Bop` acts on `Λ`. This file extends it to the sweep module
`V_k = Λ ⊗_𝕜 𝕜[y_1, …, y_k]` by letting it act on the `Λ`-factor alone, and identifies Carlsson
and Mellit's lowering operator on a power of the last variable: `d_-(y_kⁱ F) = -B_{i+1}F`.

## Main definitions

* `HJO.Sweep.bopExt`, the operator `B_r` on `V_k`.

## Main results

* `HJO.Sweep.bopExt_monomial`, `HJO.Sweep.bopExt_monomial_mul`, `HJO.Sweep.bopExt_mem_piece`:
  the prescription, the `𝕜[y]`-linearity and the graded piece the extension preserves.
* `HJO.Sweep.dminusCM_auxVar_pow_mul`.

## Implementation notes

**The extension is the coefficientwise application.** In the one-total-space convention of
`HJO.Shuffle.SweepModule` the auxiliary variables are *outside* and `Λ` sits in the
coefficient ring, so the prescription "send `f y_1^{a_1} ⋯ y_k^{a_k}` to
`(B_r f) y_1^{a_1} ⋯ y_k^{a_k}`" is literally application of `B_r` to each coefficient of a
polynomial in the `y`. That is `AddMonoidAlgebra.map` of the underlying additive map, which is why
nothing here needs a basis: `bopExt_monomial` is the prescription and `bopExt_monomial_mul` is the
`𝕜[y]`-linearity, both read off the coefficients. `B_r` is only `𝕜`-linear and *not* `Λ`-linear, so
the extension is a `Module.End L (Total L)` and not a `Λ`-linear map; that is the one respect in
which it differs from the operators on the sweep module that are built from
`MvPolynomial.aevalTower`.

**The displacement and `τ^-_{k,k}` are the same substitution read in two variables.** The
proof of `HJO.Sweep.dminusCM_auxVar_pow_mul` turns on this: `β` sends `p_r` to
`p_r + (1 - q^r)z^{-r}` and `τ^-_{k,k}` sends `p_r` to `p_r + (1 - q^r)y_k^r`, so evaluating the
displacement's variable `w = z⁻¹` at `y_k` turns one into the other. That is
`HJO.Sweep.qshiftNeg_C_eq`, and it is what makes the two sides' coefficients the same elements
`c_j` rather than merely corresponding ones.

## References

This file formalises the extension `HJO.Sweep.bopExt` of the operators to the module and the lemma
`HJO.Sweep.dminusCM_auxVar_pow_mul`, on the raising and lowering operators and the braid relations
on the module.
-/

@[expose] public section

namespace HJO.Sweep

open MvPolynomial

/-! ### The Hall--Littlewood operators on the module -/

section BopExt

variable {L : Type*} [CommRing L] [Algebra ℚ L]

/-- **The Hall--Littlewood operators on the module.** `HJO.Sweep.bopExt`: for
`k ≥ 0` and `r ∈ ℤ`, the `𝕜[y_1, …, y_k]`-linear map from `V_k` to `V_k` sending
`f y_1^{a_1} ⋯ y_k^{a_k}` to `(B_r f) y_1^{a_1} ⋯ y_k^{a_k}`.

With the auxiliary variables outside and `Λ` in the coefficient ring, that prescription is the
application of `B_r` to every coefficient; `bopExt_monomial` is the prescription itself,
`bopExt_monomial_mul` the `𝕜[y]`-linearity, and `bopExt_mem_piece` the statement that `V_k` is
carried to `V_k`. -/
@[hjo "def_cm_bop_ext"]
noncomputable def bopExt (q : L) (r : ℤ) : Module.End L (Total L) where
  toFun F := AddMonoidAlgebra.map (Sym.Bop q r).toAddMonoidHom F
  map_add' F G := AddMonoidAlgebra.map_add _ F G
  map_smul' a F := by
    simp only [RingHom.id_apply]
    refine MvPolynomial.ext _ _ fun d => ?_
    rw [MvPolynomial.coeff_addMonoidAlgebraMap, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_addMonoidAlgebraMap]
    exact (Sym.Bop q r).map_smul a _

@[simp]
theorem coeff_bopExt (q : L) (r : ℤ) (F : Total L) (d : ℕ →₀ ℕ) :
    MvPolynomial.coeff d (bopExt q r F) = Sym.Bop q r (MvPolynomial.coeff d F) := rfl

/-- **The defining prescription of the extension**: it sends `f y^d` to `(B_r f) y^d`. -/
@[hjo "def_cm_bop_ext"]
theorem bopExt_monomial (q : L) (r : ℤ) (d : ℕ →₀ ℕ) (f : Sym.Lambda L) :
    bopExt q r (MvPolynomial.monomial d f) = MvPolynomial.monomial d (Sym.Bop q r f) := by
  refine MvPolynomial.ext _ _ fun e => ?_
  rw [coeff_bopExt, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
  split_ifs with h
  · rfl
  · exact map_zero _

/-- The extension agrees with `B_r` on `Λ`, the constants of the total space. -/
theorem bopExt_C (q : L) (r : ℤ) (f : Sym.Lambda L) :
    bopExt q r (MvPolynomial.C f) = MvPolynomial.C (Sym.Bop q r f) := by
  rw [← MvPolynomial.monomial_zero', bopExt_monomial, MvPolynomial.monomial_zero']

/-- **The extension is `𝕜[y]`-linear**: it commutes with multiplication by a monomial in the
auxiliary variables. Together with its `𝕜`-linearity this is
`𝕜[y_1, …, y_k]`-linearity, every such polynomial being a `𝕜`-combination of monomials. -/
@[hjo "def_cm_bop_ext"]
theorem bopExt_monomial_mul (q : L) (r : ℤ) (d : ℕ →₀ ℕ) (F : Total L) :
    bopExt q r (MvPolynomial.monomial d 1 * F) = MvPolynomial.monomial d 1 * bopExt q r F := by
  induction F using MvPolynomial.induction_on' with
  | monomial e a =>
    rw [MvPolynomial.monomial_mul, one_mul, bopExt_monomial, bopExt_monomial,
      MvPolynomial.monomial_mul, one_mul]
  | add P Q hP hQ => rw [mul_add, map_add, map_add, hP, hQ, mul_add]

/-- **The extension carries `V_k` to `V_k`**, which is its intended domain and
codomain: applying `B_r` to a coefficient cannot introduce an auxiliary variable, so the support —
and hence the set of variables occurring — can only shrink. -/
@[hjo "def_cm_bop_ext"]
theorem bopExt_mem_piece (q : L) (r : ℤ) {k : ℕ} {F : Total L} (hF : F ∈ piece L k) :
    bopExt q r F ∈ piece L k := by
  rw [piece, MvPolynomial.mem_supported] at hF ⊢
  intro n hn
  obtain ⟨d, hd, hnd⟩ := MvPolynomial.mem_vars_iff_mem_support n |>.1 hn
  refine hF (MvPolynomial.mem_vars_iff_mem_support n |>.2 ⟨d, ?_, hnd⟩)
  rw [MvPolynomial.mem_support_iff] at hd ⊢
  rw [coeff_bopExt] at hd
  exact fun h => hd (by rw [h, map_zero])

end BopExt

/-! ### The lowering operator on a power of the last variable -/

section DminusBop

variable {L : Type*} [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in
/-- `τ^-_{k,k}` fixes a monomial in the auxiliary variables. -/
theorem qshiftNeg_monomial (q : L) (m : ℕ) (d : ℕ →₀ ℕ) :
    qshiftNeg q m (MvPolynomial.monomial d (1 : Sym.Lambda L))
      = MvPolynomial.monomial d (1 : Sym.Lambda L) := by
  rw [MvPolynomial.monomial_eq, map_one, map_mul, map_one, one_mul, one_mul, Finsupp.prod,
    map_prod]
  exact Finset.prod_congr rfl fun n _ => by rw [map_pow, qshiftNeg_auxVar]

omit [Algebra ℚ L] in
/-- **`τ^-_{k,k}` is the displacement `β` with its variable evaluated at `y_k`.** Both sides are
ring homomorphisms out of `Λ`; on the power sum `p_r` the left gives
`p_r - (q^r - 1)y_k^r` and the right `p_r + (1 - q^r)y_k^r`, which is the same element. -/
theorem qshiftNeg_C_eq (q : L) (k : ℕ) (f : Sym.Lambda L) :
    qshiftNeg q (k + 1) (MvPolynomial.C f)
      = Polynomial.eval₂ (MvPolynomial.C : Sym.Lambda L →+* Total L) (MvPolynomial.X k)
          (Sym.plethHallLittlewood q f) := by
  have h : ((qshiftNeg q (k + 1) : Total L →+* Total L).comp
        (MvPolynomial.C : Sym.Lambda L →+* Total L))
      = (Polynomial.eval₂RingHom (MvPolynomial.C : Sym.Lambda L →+* Total L)
          (MvPolynomial.X k)).comp
        (Sym.plethHallLittlewood q : Sym.Lambda L →+* Polynomial (Sym.Lambda L)) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · have hmap : (MvPolynomial.C (MvPolynomial.C a : Sym.Lambda L) : Total L)
          = algebraMap L (Total L) a := by
        rw [IsScalarTower.algebraMap_apply L (Sym.Lambda L) (Total L) a,
          MvPolynomial.algebraMap_eq, MvPolynomial.algebraMap_eq]
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_coe, RingHom.coe_coe, hmap,
        AlgHom.commutes, Sym.plethHallLittlewood_C, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C, hmap]
    · have hps : Sym.powerSum L (i + 1) = (MvPolynomial.X i : Sym.Lambda L) := by
        rw [Sym.powerSum, Nat.add_sub_cancel]
      have hav : (auxVar (k + 1) : Total L) = MvPolynomial.X k := by
        rw [auxVar, Nat.add_sub_cancel]
      have hL : qshiftNeg q (k + 1) (MvPolynomial.C (MvPolynomial.X i : Sym.Lambda L))
          = MvPolynomial.C (MvPolynomial.X i : Sym.Lambda L)
            - scal (q ^ (i + 1) - 1) * (MvPolynomial.X k : Total L) ^ (i + 1) := by
        rw [← hps, qshiftNeg_powerSum, hav]
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_coe, RingHom.coe_coe, hL,
        Sym.plethHallLittlewood_X, hps]
      simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_add, Polynomial.eval₂_mul,
        Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X]
      rw [scal, show (1 : L) - q ^ (i + 1) = -(q ^ (i + 1) - 1) by ring, map_neg, map_neg]
      ring
  exact congrArg (fun g : Sym.Lambda L →+* Total L => g f) h

/-- Carlsson and Mellit's lowering operator on `y_kⁱ f` for a symmetric function `f`: the special
case of
`HJO.Sweep.dminusCM_auxVar_pow_mul` at which the computation happens. -/
theorem dminusCM_auxVar_pow_mul_C (q : L) (k i : ℕ) (f : Sym.Lambda L) :
    dminusCM q (k + 1) ((auxVar (k + 1) : Total L) ^ i * MvPolynomial.C f)
      = -MvPolynomial.C (Sym.Bop q ((i : ℤ) + 1) f) := by
  have hav : (auxVar (k + 1) : Total L) = MvPolynomial.X k := by rw [auxVar, Nat.add_sub_cancel]
  set P := Sym.plethHallLittlewood q f with hP
  have hstep : qshiftNeg q (k + 1) ((auxVar (k + 1) : Total L) ^ i * MvPolynomial.C f)
      = ∑ j ∈ P.support,
          MvPolynomial.monomial (Finsupp.single k (i + j)) (P.coeff j) := by
    rw [map_mul, map_pow, hav, qshiftNeg_auxVar, qshiftNeg_C_eq, Polynomial.eval₂_eq_sum,
      Polynomial.sum_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hm : (MvPolynomial.monomial (Finsupp.single k (i + j)) (P.coeff j) : Total L)
        = MvPolynomial.C (P.coeff j) * (MvPolynomial.X k : Total L) ^ (i + j) := by
      rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial, mul_one]
    rw [hm, pow_add]
    ring
  rw [dminusCM_succ_apply, hstep, map_sum]
  have hone : (-1 : Total L) = MvPolynomial.C (-1 : Sym.Lambda L) := by
    rw [map_neg, map_one]
  have hterm : ∀ j ∈ P.support,
      lowerCoeffShift L k (MvPolynomial.monomial (Finsupp.single k (i + j)) (P.coeff j))
        = -MvPolynomial.C (P.coeff j * Sym.elemSymmAlt L ((i : ℤ) + 1 + j)) := by
    intro j _
    have hs : (Finsupp.single k (i + j)) k = i + j := Finsupp.single_eq_same
    have he : Finsupp.erase k (Finsupp.single k (i + j)) = 0 := Finsupp.erase_single
    have hcast : ((i : ℤ) + 1 + j) = ((i + j + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [lowerCoeffShift_monomial', hs, he, MvPolynomial.monomial_zero', MvPolynomial.C_1, mul_one,
      hcast, Sym.elemSymmAlt_natCast, MvPolynomial.C_mul, MvPolynomial.C_mul,
      MvPolynomial.C_pow, ← hone]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, ← map_sum]
  congr 1

/-- **The lowering operator on a power of the last variable.**
`HJO.Sweep.dminusCM_auxVar_pow_mul`: for every `k ≥ 1`, every `i ≥ 0` and every `F ∈ V_{k-1}`,
`d_-(y_kⁱ F) = -B_{i+1}F`, the right-hand side being the extension `HJO.Sweep.bopExt` of the
operator to the module.

Here the `k` is `k + 1`, so `F` ranges over `V_k`. -/
@[hjo "lem_cm_dminus_bop"]
theorem dminusCM_auxVar_pow_mul (q : L) (k i : ℕ) {F : Total L} (hF : F ∈ piece L k) :
    dminusCM q (k + 1) ((auxVar (k + 1) : Total L) ^ i * F)
      = -bopExt q ((i : ℤ) + 1) F := by
  conv_lhs => rw [F.as_sum]
  rw [Finset.mul_sum, map_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : d k = 0 := exponent_eq_zero_of_mem_piece hF hd
  have hrw : (auxVar (k + 1) : Total L) ^ i * MvPolynomial.monomial d (MvPolynomial.coeff d F)
      = MvPolynomial.monomial d 1 *
        ((auxVar (k + 1) : Total L) ^ i * MvPolynomial.C (MvPolynomial.coeff d F)) := by
    rw [show (MvPolynomial.monomial d (MvPolynomial.coeff d F) : Total L)
        = MvPolynomial.monomial d 1 * MvPolynomial.C (MvPolynomial.coeff d F) by
      rw [mul_comm, MvPolynomial.C_mul_monomial, mul_one]]
    ring
  rw [hrw, dminusCM_succ_apply, map_mul, qshiftNeg_monomial,
    lowerCoeffShift_monomial_mul hd0 1, ← dminusCM_succ_apply,
    dminusCM_auxVar_pow_mul_C, bopExt_monomial, mul_neg]
  rw [show (MvPolynomial.monomial d (Sym.Bop q ((i : ℤ) + 1) (MvPolynomial.coeff d F)) : Total L)
      = MvPolynomial.monomial d 1 *
        MvPolynomial.C (Sym.Bop q ((i : ℤ) + 1) (MvPolynomial.coeff d F)) by
    rw [mul_comm, MvPolynomial.C_mul_monomial, mul_one]]

end DminusBop

end HJO.Sweep
