/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.BopModule
public meta import HJO.Attr

/-! # The modified lowering operator on a power of the last variable

`HJO.Sweep.dminusCM_auxVar_pow_mul` computes Carlsson and Mellit's lowering operator on `y_k^iF`:
`d_-(y_k^iF) = -B_{i+1}F`. This file is the same computation for the *modified* operator `d^♭_-` of
`HJO.Sweep.dminus`, which is what `HJO.Sweep.dminus_auxVar_pow_mul` asks for:

`d^♭_-(y_k^iF) = B_iF`,

with neither the sign nor the index shift. The two differences are the single difference between the
two operators: `HJO.Sweep.lowerCoeff` pairs the coefficient of `y_k^j` with `(-1)^je_j` where
`HJO.Sweep.lowerCoeffShift` pairs it with `(-1)^je_{j+1}`, so the elementary function met by the
`j`-th coefficient of `y_k^iF` is `e_{i+j}` rather than `e_{i+j+1}`; and
`HJO.Sym.elemSymmAlt ((i:ℤ)+j) = (-1)^{i+j}e_{i+j}` carries the sign that the unmodified computation
has to pull out as a global `-1`.

At `i = 0` and `F = 1` this reads `d^♭_-(1) = B_0(1) = e_0 = 1`, which is the first generator of
Mellit's kernel ideal evaluated on the vacuum; the unmodified operator gives `e_1` there
(`HJO.Sweep.dminusCM_one`), so the two operators are separated already at this value.

## Main results

* `HJO.Sweep.dminus_auxVar_pow_mul`.
* `HJO.Sweep.dminus_auxVar_pow_mul_C` — the same on a bare symmetric function, which is where the
  computation happens.

## Implementation notes

The proof is `HJO.Sweep.dminusCM_auxVar_pow_mul`'s, letter for letter, and shares its two structural
inputs: `HJO.Sweep.qshiftNeg_C_eq`, which identifies `τ^-_{k,k}` on `Λ` with the Hall–Littlewood
displacement `β` evaluated at `y_k` — so that the coefficients `c_j` of the proof are
the same elements on both sides rather than merely corresponding ones — and
`HJO.Sweep.lowerCoeff_mul_of_mem_piece`, which lets the `y`-monomials of `F` come out of the
extraction, this being where `F ∈ V_{k-1}` is spent. That hypothesis is *not* decoration: at
`F = y_k` the extraction meets a further power of `y_k` and the identity fails.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, §3.
-/

@[expose] public section

namespace HJO.Sweep

section DminusBopMod

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The modified lowering operator on `y_k^i f` for a symmetric function `f`**: the special case
of `HJO.Sweep.dminus_auxVar_pow_mul` at which the computation happens, `d^♭_-(y_k^if) = B_if`.

`τ^-_{k,k}` fixes `y_k` and, on `Λ`, is the Hall–Littlewood displacement evaluated at `y_k`
(`HJO.Sweep.qshiftNeg_C_eq`), so `τ^-_{k,k}(y_k^if) = ∑_j c_j y_k^{i+j}` with `c_j` the coefficients
of `βf`. The extraction then meets `(-1)^{i+j}e_{i+j}` on each, which is
`HJO.Sym.elemSymmAlt ((i:ℤ)+j)`, and the resulting sum is `B_if` on the nose. -/
theorem dminus_auxVar_pow_mul_C (q : L) (k i : ℕ) (f : Sym.Lambda L) :
    dminus q (k + 1) ((auxVar (k + 1) : Total L) ^ i * MvPolynomial.C f)
      = MvPolynomial.C (Sym.Bop q (i : ℤ) f) := by
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
  rw [dminus_succ_apply, hstep, map_sum]
  have hone : (-1 : Total L) = MvPolynomial.C (-1 : Sym.Lambda L) := by
    rw [map_neg, map_one]
  have hterm : ∀ j ∈ P.support,
      lowerCoeff L k (MvPolynomial.monomial (Finsupp.single k (i + j)) (P.coeff j))
        = MvPolynomial.C (P.coeff j * Sym.elemSymmAlt L ((i : ℤ) + j)) := by
    intro j _
    have hs : (Finsupp.single k (i + j)) k = i + j := Finsupp.single_eq_same
    have he : Finsupp.erase k (Finsupp.single k (i + j)) = 0 := Finsupp.erase_single
    have hcast : ((i : ℤ) + j) = ((i + j : ℕ) : ℤ) := by push_cast; ring
    rw [lowerCoeff_monomial', hs, he, MvPolynomial.monomial_zero', MvPolynomial.C_1, mul_one,
      hcast, Sym.elemSymmAlt_natCast, MvPolynomial.C_mul, MvPolynomial.C_mul,
      MvPolynomial.C_pow, ← hone]
  rw [Finset.sum_congr rfl hterm, ← map_sum, Sym.bop_apply, Polynomial.sum_def, ← hP]

/-- **The modified lowering operator on a power of the last variable.** This is
`HJO.Sweep.dminus_auxVar_pow_mul`: for every `k ≥ 1`, every `i ≥ 0` and every `F ∈ V_{k-1}`,
`d^♭_-(y_k^iF) = B_iF`, the right-hand side being the extension `HJO.Sweep.bopExt` of `B_i` to the
module.

Here the `k` is `k + 1`, so `F` ranges over `V_k`. Reducing to
`HJO.Sweep.dminus_auxVar_pow_mul_C` is the `y`-monomial expansion of `F`: each monomial of `F` is
free of `y_{k+1}` (`HJO.Sweep.exponent_eq_zero_of_mem_piece`), so it passes both `τ^-_{k+1,k+1}` and
the extraction, and `HJO.Sweep.bopExt` acts on its `Λ`-coefficient alone. -/
@[hjo "lem_vmod_dminus_bop_mod"]
theorem dminus_auxVar_pow_mul (q : L) (k i : ℕ) {F : Total L} (hF : F ∈ piece L k) :
    dminus q (k + 1) ((auxVar (k + 1) : Total L) ^ i * F) = bopExt q (i : ℤ) F := by
  conv_lhs => rw [F.as_sum]
  rw [Finset.mul_sum, map_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : d k = 0 := exponent_eq_zero_of_mem_piece hF hd
  have hrw : (auxVar (k + 1) : Total L) ^ i * MvPolynomial.monomial d (MvPolynomial.coeff d F)
      = MvPolynomial.monomial d 1 *
        ((auxVar (k + 1) : Total L) ^ i * MvPolynomial.C (MvPolynomial.coeff d F)) := by
    rw [show (MvPolynomial.monomial d (MvPolynomial.coeff d F) : Total L)
        = MvPolynomial.monomial d 1 * MvPolynomial.C (MvPolynomial.coeff d F) by
      rw [mul_comm, MvPolynomial.C_mul_monomial, mul_one]]
    ring
  rw [hrw, dminus_succ_apply, map_mul, qshiftNeg_monomial,
    lowerCoeff_monomial_mul hd0 1, ← dminus_succ_apply,
    dminus_auxVar_pow_mul_C, bopExt_monomial]
  rw [show (MvPolynomial.monomial d (Sym.Bop q (i : ℤ) (MvPolynomial.coeff d F)) : Total L)
      = MvPolynomial.monomial d 1 *
        MvPolynomial.C (Sym.Bop q (i : ℤ) (MvPolynomial.coeff d F)) by
    rw [mul_comm, MvPolynomial.C_mul_monomial, mul_one]]

end DminusBopMod

end HJO.Sweep
