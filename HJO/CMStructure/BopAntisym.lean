/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.BopPairPhi
public import HJO.CarlssonMellit.BopModule
public meta import HJO.Attr

/-! # The Haglund--Morse--Zabrocki relation on the sweep module

`HJO.Sym.bop_pair_antisymm` is a relation between the operators `B_r` of `HJO.Sym.Bop` on `Λ`. Their
extensions `HJO.Sweep.bopExt` to the sweep module act on the `Λ`-coefficients
of a polynomial in the auxiliary variables and on nothing else, so the relation holds there
coefficientwise, with no reduction from `V_k` to `Λ` to perform.

## Main results

* `HJO.Sweep.bopExt_hmz` — the relation itself on the module:
  `B_mB_nH - qB_{m+1}B_{n-1}H = qB_nB_mH - B_{n-1}B_{m+1}H`.
* `HJO.Sweep.bopExt_pair_antisymm`, the same relation re-parametrised by
  `m = a+1`, `n = b+2`: the combination `E a b = qB_{a+2}B_{b+1} - B_{a+1}B_{b+2}` is antisymmetric
  in `a` and `b`.

## Implementation notes

**Both indices range over `ℤ`, where the statement is usually made for `a, b ≥ 0`.** The
non-negativity is not used: `HJO.Sym.Bop` and `HJO.Sweep.bopExt` give `B_r` for every integer `r`,
and the underlying Haglund--Morse--Zabrocki relation is itself stated for integer indices. The
`a, b ≥ 0` comes from its one use, where `a` and `b` are exponents of `y_{k-1}, y_k`, and that use
instantiates at `(a : ℤ)`, `(b : ℤ)` with nothing to discharge.

**The hypothesis `H ∈ V_k` is dropped.** `HJO.Sweep.bopExt` is an endomorphism of the whole total
space, carrying `V_k` to `V_k` (`bopExt_mem_piece`), so the identity on `V_k` is the restriction of
one that holds everywhere; the level `k` of the statement enters nowhere in the proof.

**The scalar is written `q • P`** for `q : L`, and not as multiplication by the doubly constant
polynomial `HJO.Sweep.scal q`: the two agree, but `HJO.Sweep.scal` is defined only over a field,
while everything here lives over a commutative `ℚ`-algebra, the weakest base `HJO.Sweep.bopExt`
needs. The lemma using it, which works over a field, converts with `HJO.Sweep.scal_mul_eq_smul`. On
the `Λ`-coefficients the action is multiplication by `MvPolynomial.C q`
(`MvPolynomial.smul_eq_C_mul`), which is how the coefficientwise reduction meets the `q •` of
`HJO.Sym.bop_pair_antisymm_apply`.

**On the diagonal the antisymmetry degenerates into a commutation law**: at `a = b` it reads
`E a a = -E a a`, hence `qB_{a+2}B_{a+1} = B_{a+1}B_{a+2}` since `2` is invertible. That is not a
triviality — the operators do not commute, `B_1B_01 = -e_1` while `B_0B_11 = -qe_1`.

## References

In E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, it is the antisymmetry asserted
inside the proof of Lemma 5.3. `HJO.Sweep.bopExt_pair_antisymm` uses `HJO.Sweep.piece`,
`HJO.Sym.Bop` and `HJO.Sweep.bopExt`, and is proved from `HJO.Sym.bop_pair_antisymm` at `m = a+1`,
`n = b+2`; it is consumed by `HJO.Sweep.dminusCM_dminusCM_braid`.
-/

@[expose] public section

namespace HJO.Sweep

section Antisym

variable {L : Type*} [CommRing L] [Algebra ℚ L]

/-- **The Haglund--Morse--Zabrocki relation on the sweep module**: for all integers `m, n` and every
`H` in the total space,

`B_mB_nH - qB_{m+1}B_{n-1}H = qB_nB_mH - B_{n-1}B_{m+1}H`,

the operators being the extensions `HJO.Sweep.bopExt`. Since the extension
applies `B_r` to each `Λ`-coefficient (`HJO.Sweep.coeff_bopExt`), this is
`HJO.Sym.bop_pair_antisymm_apply` read on each coefficient separately. -/
theorem bopExt_hmz (q : L) (m n : ℤ) (H : Total L) :
    bopExt q m (bopExt q n H) - q • bopExt q (m + 1) (bopExt q (n - 1) H)
      = q • bopExt q n (bopExt q m H) - bopExt q (n - 1) (bopExt q (m + 1) H) := by
  refine MvPolynomial.ext _ _ fun d => ?_
  have h := Sym.bop_pair_antisymm_apply q m n (MvPolynomial.coeff d H)
  simp only [MvPolynomial.smul_eq_C_mul] at h
  simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, coeff_bopExt,
    MvPolynomial.smul_eq_C_mul]
  exact h

/-- **The antisymmetry of a shifted pair of operators.** For all indices
`a, b` and every `H` in the total space,

`qB_{a+2}(B_{b+1}H) - B_{a+1}(B_{b+2}H) = -(qB_{b+2}(B_{a+1}H) - B_{b+1}(B_{a+2}H))`.

This is `HJO.Sweep.bopExt_hmz` at `m = a+1`, `n = b+2`, which turns the involution
`(m,n) ↦ (n-1, m+1)` of that relation into the interchange of `a` and `b`, with both sides
negated. -/
@[hjo "lem_cm_bop_antisym"]
theorem bopExt_pair_antisymm (q : L) (a b : ℤ) (H : Total L) :
    q • bopExt q (a + 2) (bopExt q (b + 1) H) - bopExt q (a + 1) (bopExt q (b + 2) H)
      = -(q • bopExt q (b + 2) (bopExt q (a + 1) H)
          - bopExt q (b + 1) (bopExt q (a + 2) H)) := by
  have h := bopExt_hmz q (a + 1) (b + 2) H
  rw [show a + 1 + 1 = a + 2 by ring, show b + 2 - 1 = b + 1 by ring] at h
  rw [← h, neg_sub]

end Antisym

end HJO.Sweep
