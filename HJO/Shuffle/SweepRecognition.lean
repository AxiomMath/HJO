/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitShiftGenerators
public import HJO.CMStructure.DemazureIdentities
public meta import HJO.Attr

/-! # Recognising the braid operator and the lowering operator of the sweep

For `k ≥ 2` and `1 ≤ i ≤ k-1` the braid operator of the sweep is the `Λ`-linear endomorphism
`T_iF = s_iF + (q-1)y_i∂_iF` of `V_k = Λ ⊗_𝕜 𝕜[y_1, …, y_k]`, where `s_i` interchanges `y_i` and
`y_{i+1}` and `∂_i` is the divided difference; for `k ≥ 1` the lowering operator
`d_- : V_k → V_{k-1}` sends `F` to the coefficient of `y_k^0` in
`τ^-_{k,k}(F)·∑_{n ≥ 0}(-1)^ne_ny_k^{-n}`. They are
`HJO.Sweep.braid` and `HJO.Sweep.dminus`, defined in `HJO/Shuffle/SweepModule.lean` on the
divided difference and on the virtual-alphabet substitution `τ^-_{k,k}`. This file supplies the two
statements that let each be used without unfolding it: the property that identifies `T_i` among all
candidates, and the rule that evaluates `d_-` on a `y_k`-expansion.

`T_i` is identified by Mellit's defining formula for it (§3.2), cleared of its denominator,
`(y_{i+1}-y_i)T_iF = (q-1)y_iF + (y_{i+1}-qy_i)s_iF`. The auxiliary variables are distinct, so
`y_{i+1}-y_i` is a non-zerodivisor in `Λ[y_1, y_2, …]` and that identity has at most one solution:
an operator arising from another construction — the swapping operator of the Dyck path algebra, say
— is `T_i` as soon as it satisfies the cleared identity, and no divided difference enters the
verification.

`d_-` is evaluated by expanding the series in its definition. `τ^-_{k,k}(F)` is a
polynomial in `y_k`, say `∑_j A_jy_k^j` with every `A_j` in `V_{k-1}`; each `A_j` is free of `y_k`,
so the coefficient of `y_k^0` in `A_jy_k^j·∑_n(-1)^ne_ny_k^{-n}` is the single term `n = j`, and
`d_-F = ∑_j (-1)^je_jA_j`. This is the expanded form of the operator, with the series that produces
it discharged.

## Main results

* `HJO.Sweep.eq_braid`: the cleared identity determines `T_iF`, for `i ≥ 1`.
* `HJO.Sweep.dminus_succ_eq_sum_of_qshiftNeg`: the value of `d_-` on a `y_k`-expansion of
  `τ^-_{k,k}(F)` whose coefficients lie in `V_{k-1}`.
* `HJO.Sweep.lowerCoeff_auxVar_pow`: the extraction of `d_-` against a power of the last letter,
  `y_k^m ↦ (-1)^me_m`.

## Implementation notes

The lowering operator is stated here at index `k+1`, so that its codomain `V_k` is named without
truncated subtraction; this is the convention of `HJO.Sweep.dminus_succ_apply`. Its expansion is
indexed by an arbitrary finite set of exponents rather than by a range: the hypothesis is then an
equation between two elements of the total space that a caller can discharge by whatever expansion
is at hand, and no exponent bound has to be produced.

The recognition statement for `T_i` is pointwise and carries no linearity hypothesis. The cleared
identity pins the value at each `F` on its own, so the hypothesis of `Λ`-linearity that the
definition of `T_i` carries is not needed to recognise it, and a candidate known only as a function
is covered.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, §5, and A. Mellit,
*Toric braids and `(m,n)`-parking functions*, §3.2.
-/

@[expose] public section

attribute [hjo "def_sweep_braid"] HJO.Sweep.braid HJO.Sweep.braid_apply
attribute [hjo "def_sweep_dminus"] HJO.Sweep.dminus HJO.Sweep.dminus_apply

namespace HJO.Sweep

section Field

variable {L : Type*} [Field L]

/-- **The cleared identity determines `T_i`.** For `i ≥ 1`, an element `G` of the total space with
`(y_{i+1}-y_i)G = (q-1)y_iF + (y_{i+1}-qy_i)s_iF` is `T_iF`: the braid operator satisfies that
identity (`HJO.Sweep.auxVar_sub_mul_braid`) and `y_{i+1}-y_i` is a non-zerodivisor.

This is how an operator built elsewhere is recognised as the braid operator of the sweep, the
verification staying inside the ring `Λ[y_1, y_2, …]` and never mentioning the divided difference.
The hypothesis `1 ≤ i` cannot be dropped: at the unread index `0` the convention `y_0 = y_1` makes
both sides of the identity vanish, and every `G` satisfies it. -/
@[hjo "def_sweep_braid"]
theorem eq_braid {q : L} {i : ℕ} (hi : 1 ≤ i) {F G : Total L}
    (h : ((auxVar (i + 1) : Total L) - auxVar i) * G
      = scal (q - 1) * auxVar i * F
        + ((auxVar (i + 1) : Total L) - scal q * auxVar i) * swapAux L i F) :
    G = braid q i F :=
  mul_left_cancel₀ (auxVar_sub_ne_zero hi) (h.trans (auxVar_sub_mul_braid q i F).symm)

end Field

section Newton

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The extraction of `d_-` against a power of the last letter:** `y_{j+1}^m ↦ (-1)^me_m`. The
coefficient of `y_{j+1}^0` in `y_{j+1}^m·∑_n(-1)^ne_ny_{j+1}^{-n}` is the single term `n = m`. -/
theorem lowerCoeff_auxVar_pow (j m : ℕ) :
    lowerCoeff L j ((auxVar (j + 1) : Total L) ^ m)
      = (-1 : Total L) ^ m * MvPolynomial.C (Sym.elemSymm L m) := by
  have hav : (auxVar (j + 1) : Total L) = MvPolynomial.X j := by
    rw [auxVar, Nat.add_sub_cancel]
  rw [hav, MvPolynomial.X_pow_eq_monomial, lowerCoeff_monomial]
  simp

/-- **The lowering operator on a `y_k`-expansion.** If `τ^-_{k,k}(F) = ∑_j A_jy_k^j` with every
`A_j` in `V_{k-1}`, then `d_-F = ∑_j (-1)^je_jA_j`: this is the coefficient of `y_k^0` in
`τ^-_{k,k}(F)·∑_n(-1)^ne_ny_k^{-n}`, the series contributing its term `n = j` against `A_jy_k^j`
and nothing else, because `A_j` is free of `y_k`.

The index is `k+1` here, so that the coefficients lie in `V_k` and the codomain is named without
truncated subtraction. The set of exponents is an arbitrary finite one: any expansion of
`τ^-_{k,k}(F)` in the last letter, however produced, discharges the hypothesis. -/
@[hjo "def_sweep_dminus"]
theorem dminus_succ_eq_sum_of_qshiftNeg {q : L} {k : ℕ} {F : Total L} {s : Finset ℕ}
    {A : ℕ → Total L} (hA : ∀ j ∈ s, A j ∈ piece L k)
    (hF : qshiftNeg q (k + 1) F = ∑ j ∈ s, A j * (auxVar (k + 1) : Total L) ^ j) :
    dminus q (k + 1) F
      = ∑ j ∈ s, (-1 : Total L) ^ j * MvPolynomial.C (Sym.elemSymm L j) * A j := by
  rw [dminus_succ_apply, hF, map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [lowerCoeff_mul_of_mem_piece (hA j hj), lowerCoeff_auxVar_pow]
  ring

end Newton

end HJO.Sweep
