/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.ChiPrimeLower
public import HJO.CarlssonMellit.ChiPrimeSwapFree
public import HJO.CarlssonMellit.ChiPrimeZGraded
public import HJO.CarlssonMellit.LowerTuples
public import HJO.CarlssonMellit.ZvarMerged
public meta import HJO.Attr

/-! # The freed pieces are related by a swapping operator

`HJO.Dyck.isZDelta_zvar_mul_lowerCharPiece`: for a partial Dyck path `π ∈ 𝔻_{k,N}` of level
`k = m + 1` and every `r ≥ 0`,

`z^{(k)}_{k+r+1} μ_{r+1}(π) = Δ_{k+r}(z^{(k)}_{k+r} μ_r(π))`.

This is the swapping identity `HJO.Dyck.isZDelta_auxToFrac_unnormalisedCharSeries` read at the lower
tuple `σ^{[r]}`, with the prescribed auxiliary factor `y_1 ⋯ y_{k-1}` cancelled. The tuple side is
`HJO.Dyck.transposeTuple_lowerTuple`: the entry `k + r` occurs in `σ^{[r]}`, at the last position,
and no entry equals `k + r + 1`, so `τ_{k+r}σ^{[r]} = σ^{[r+1]}`. The factorisation of the two
characteristic series is `HJO.Dyck.unnormalisedCharSeries_lowerTuple`, and the cancellation is the
point of this file: `y_1 ⋯ y_{k-1}` is a *constant* series whose coefficient is a nonzero element of
the lower coefficient field `𝕂(y_1, …, y_{k-1})`, hence a unit of it, so the inverse constant is
again a member of `Z^{(k+1)}` fixed by `ŝ_{k+r}` and `HJO.Sym.isZDelta_mul_of_zSwap_eq` multiplies
it through. No appeal to `HJO.Sym.isDomain_auxAlphabetSeriesFrac` is needed: the factor is not
cancelled, it is inverted.

Note that the identity is *not* `μ_{r+1}(π) = Δ_{k+r}(μ_r(π))`. The factor `y_1 ⋯ y_{k-1}` is
`ŝ_{k+r}`-invariant and pulls through, but `z^{(k)}_{k+r}` is one of the two letters the operator
interchanges and does not.

## Main results

* `HJO.Dyck.transposeTuple_lowerTuple`: `τ_{k+r}σ^{[r]} = σ^{[r+1]}`.
* `HJO.Sym.isZDelta_of_isZDelta_C_mul`: the cancellation, as a statement about an arbitrary
  constant series with invertible coefficient in the lower field.
* `HJO.Dyck.isZDelta_zvar_mul_lowerCharPiece_of_isZDelta`: the reduction, with the swapping identity
  at `σ^{[r]}` as a hypothesis.
* `HJO.Dyck.isZDelta_zvar_mul_lowerCharPiece`: the identity, that hypothesis discharged by
  `HJO.Dyck.isZDelta_auxToFrac_unnormalisedCharSeries`.

## Implementation notes

*The reduction is separated from the main result.*
`HJO.Dyck.isZDelta_zvar_mul_lowerCharPiece_of_isZDelta` carries the swapping identity at `σ^{[r]}`
as a hypothesis and asks nothing of the path beyond `k ≤ N`; the main result adds only the
instantiation of `HJO.Dyck.isZDelta_auxToFrac_unnormalisedCharSeries`, whose hypotheses at the lower
tuple are `HJO.Dyck.lowerTuple_injective`, `HJO.Dyck.lowerTuple_last` and the vacuity of the
ordering condition — no entry of `σ^{[r]}` equals `k + r + 1`.

*The level is `m + 1` and the operator is indexed by the offset.* `HJO.Sym.IsZDelta q r` is the
operator `Δ_m` at `m = k + r` for the level `k = m + 1` of this file, interchanging the merged
variables `HJO.Sym.zvar K (m+1) (m+r)` and `HJO.Sym.zvar K (m+1) (m+r+1)`; labels are `0`-based, so
the `z^{(k)}_{k+r}` is the former. No `ℕ`-subtraction appears.

## References

E. Carlsson and A. Mellit, *A proof of the
shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, equation (4.11).
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K] [IsDomain K] {k : ℕ}

/-- **A constant series with a unit coefficient in the lower field cancels from the swapping
equation.** The constant series of an element of `𝕂(y_1, …, y_k)` lies in `Z^{(k+1)}` and is fixed
by `ŝ_m`, so `HJO.Sym.isZDelta_mul_of_zSwap_eq` multiplies the inverse constant through the equation
of `HJO.Sym.IsZDelta`; the two constants then collapse to `1`. -/
theorem isZDelta_of_isZDelta_C_mul {q : K} {r : ℕ} {c : AuxFrac K k} (hc : c ≠ 0)
    {F H : AuxAlphabetSeriesFrac K (k + 1)}
    (hF : MvPowerSeries.C (auxFracCastSucc K k c) * F ∈ zRing K k)
    (h : IsZDelta q r (MvPowerSeries.C (auxFracCastSucc K k c) * F)
      (MvPowerSeries.C (auxFracCastSucc K k c) * H)) :
    IsZDelta q r F H := by
  have hCmul : ∀ a b : AuxFrac K (k + 1),
      (MvPowerSeries.C a : AuxAlphabetSeriesFrac K (k + 1)) * MvPowerSeries.C b
        = MvPowerSeries.C (a * b) := fun a b => (map_mul _ a b).symm
  have hcollapse : ∀ G : AuxAlphabetSeriesFrac K (k + 1),
      MvPowerSeries.C (auxFracCastSucc K k c⁻¹)
          * (MvPowerSeries.C (auxFracCastSucc K k c) * G) = G := fun G => by
    rw [← mul_assoc, hCmul, ← map_mul, inv_mul_cancel₀ hc]
    simp
  have hg := isZDelta_mul_of_zSwap_eq (r := r) hF (C_auxFracCastSucc_mem_zRing c⁻¹)
    (by rw [zSwap_apply, zPerm_C]) h
  rwa [hcollapse F, hcollapse H] at hg

end HJO.Sym

namespace HJO.Dyck

open HJO.Sym

/-! ### Transposing the freed label of the lower tuple -/

/-- **Transposing the freed label advances the lower tuple**: `τ_{k+r}σ^{[r]} = σ^{[r+1]}`. The
entries of `σ^{[r]}` are the labels `0, …, k-2` and the freed label `k-1+r`; the transposition
carries the freed label to `k+r` and fixes the others, every one of them being smaller than
`k - 1 + r`. -/
theorem transposeTuple_lowerTuple (m r : ℕ) :
    transposeTuple (m + r) (lowerTuple m r) = lowerTuple m (r + 1) := by
  refine funext fun i => ?_
  simp only [transposeTuple, Function.comp_apply]
  induction i using Fin.lastCases with
  | last =>
    rw [lowerTuple_last, Equiv.swap_apply_left, lowerTuple_last]
    omega
  | cast j =>
    have hj := j.isLt
    rw [lowerTuple_castSucc, lowerTuple_castSucc,
      Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]

/-! ### The prescribed auxiliary factor -/

variable {K : Type*} [CommRing K] [IsDomain K] {N : ℕ}

/-- The product `y_1 ⋯ y_{k-1}` of the auxiliary variables the lower tuple prescribes, as an element
of the lower coefficient field `𝕂(y_1, …, y_{k-1})`. At `k = 1` it is the empty product `1`. -/
noncomputable def lowerAuxScalar (K : Type*) [CommRing K] [IsDomain K] (m : ℕ) : AuxFrac K m :=
  algebraMap (MvPolynomial (Fin m) K) (AuxFrac K m) (∏ j : Fin m, MvPolynomial.X j)

/-- The prescribed auxiliary factor is nonzero: it is the image of a product of distinct variables
under the injective localization map of a domain. -/
theorem lowerAuxScalar_ne_zero (K : Type*) [CommRing K] [IsDomain K] (m : ℕ) :
    lowerAuxScalar K m ≠ 0 := by
  have hp : (∏ j : Fin m, (MvPolynomial.X j : MvPolynomial (Fin m) K)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => MvPolynomial.X_ne_zero j
  intro h
  rw [lowerAuxScalar] at h
  exact hp (IsFractionRing.injective (MvPolynomial (Fin m) K) (AuxFrac K m)
    (h.trans (map_zero (algebraMap (MvPolynomial (Fin m) K) (AuxFrac K m))).symm))

/-- The prescribed auxiliary factor of `HJO.Dyck.unnormalisedCharSeries_lowerTuple`, pushed into
`P°_{k+1}`, is the constant series of `HJO.Dyck.lowerAuxScalar` included in the larger coefficient
field: the variables it names are the first `k - 1` ones, which `HJO.Sym.auxFracCastSucc` keeps. -/
theorem auxToFrac_C_prod_X_castSucc (K : Type*) [CommRing K] [IsDomain K] (m : ℕ) :
    auxToFrac K (m + 1)
        (MvPowerSeries.C (∏ j : Fin m, (MvPolynomial.X j.castSucc : MvPolynomial (Fin (m + 1)) K)))
      = MvPowerSeries.C (auxFracCastSucc K m (lowerAuxScalar K m)) := by
  have hren : MvPolynomial.rename Fin.castSucc
        (∏ j : Fin m, (MvPolynomial.X j : MvPolynomial (Fin m) K))
      = ∏ j : Fin m, (MvPolynomial.X j.castSucc : MvPolynomial (Fin (m + 1)) K) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun j _ => MvPolynomial.rename_X _ _
  rw [auxToFrac_C, lowerAuxScalar, auxFracCastSucc_algebraMap, hren]

/-! ### The freed pieces are related by a swapping operator -/

/-- **The freed pieces are related by a swapping operator**,
`HJO.Dyck.isZDelta_zvar_mul_lowerCharPiece` with the swapping identity at the lower tuple taken as a
hypothesis: if `χ'_{σ^{[r+1]}}(π) = Δ_{k+r}(χ'_{σ^{[r]}}(π))` then

`z^{(k)}_{k+r+1} μ_{r+1}(π) = Δ_{k+r}(z^{(k)}_{k+r} μ_r(π))`,

both read as the equation of `HJO.Sym.IsZDelta`. By `HJO.Dyck.unnormalisedCharSeries_lowerTuple` the
two characteristic series are the two sides of the conclusion times the constant `y_1 ⋯ y_{k-1}`,
whose coefficient is a unit of the lower coefficient field, so `HJO.Sym.isZDelta_of_isZDelta_C_mul`
removes it. -/
theorem isZDelta_zvar_mul_lowerCharPiece_of_isZDelta (q : K) {m : ℕ} {x : Fin N → ℕ}
    (hk : m + 1 ≤ N) (r : ℕ)
    (hswap : IsZDelta q r
      (auxToFrac K (m + 1) (unnormalisedCharSeries q (m + 1) x (lowerTuple m r)))
      (auxToFrac K (m + 1) (unnormalisedCharSeries q (m + 1) x (lowerTuple m (r + 1))))) :
    IsZDelta q r (auxToFrac K (m + 1) (zvar K (m + 1) (m + r) * lowerCharPiece q m x r))
      (auxToFrac K (m + 1) (zvar K (m + 1) (m + r + 1) * lowerCharPiece q m x (r + 1))) := by
  have hfac : ∀ s : ℕ, auxToFrac K (m + 1) (unnormalisedCharSeries q (m + 1) x (lowerTuple m s))
      = MvPowerSeries.C (auxFracCastSucc K m (lowerAuxScalar K m))
        * auxToFrac K (m + 1) (zvar K (m + 1) (m + s) * lowerCharPiece q m x s) := fun s => by
    rw [unnormalisedCharSeries_lowerTuple hk, mul_assoc, map_mul,
      auxToFrac_C_prod_X_castSucc]
  refine isZDelta_of_isZDelta_C_mul (lowerAuxScalar_ne_zero K m) ?_ ?_
  · rw [← hfac r]
    exact auxToFrac_unnormalisedCharSeries_mem_zRing q m x (lowerTuple m r)
  · rw [show m + r + 1 = m + (r + 1) from by omega, ← hfac r, ← hfac (r + 1)]
    exact hswap

/-! ### The main result -/

/-- **The freed pieces are related by a swapping operator**,
`HJO.Dyck.isZDelta_zvar_mul_lowerCharPiece`: for a partial Dyck path `π ∈ 𝔻_{k,N}` of level
`k = m + 1` and every `r ≥ 0`,

`z^{(k)}_{k+r+1} μ_{r+1}(π) = Δ_{k+r}(z^{(k)}_{k+r} μ_r(π))`,

read as the equation of `HJO.Sym.IsZDelta` satisfied by the pair, which by `HJO.Sym.eq_of_isZDelta`
determines the right-hand side.

`HJO.Dyck.isZDelta_auxToFrac_unnormalisedCharSeries` applies at `σ = σ^{[r]}` and `m = k + r`: the
entries of `σ^{[r]}` are pairwise distinct by `HJO.Dyck.lowerTuple_injective`, the entry `k + r`
occurs at the last position, and the ordering hypothesis is vacuous — no entry equals `k + r + 1`,
the entries below the last one being the labels `0, …, k-2`. Its conclusion at
`τ_{k+r}σ^{[r]} = σ^{[r+1]}` is then the identity above times the prescribed factor `y_1 ⋯ y_{k-1}`,
which `HJO.Dyck.isZDelta_zvar_mul_lowerCharPiece_of_isZDelta` removes. -/
@[hjo "lem_cm_mu_step"]
theorem isZDelta_zvar_mul_lowerCharPiece (q : K) {m : ℕ} {x : Fin N → ℕ}
    (hx : IsPartialDyck (m + 1) N x) (r : ℕ) :
    IsZDelta q r (auxToFrac K (m + 1) (zvar K (m + 1) (m + r) * lowerCharPiece q m x r))
      (auxToFrac K (m + 1) (zvar K (m + 1) (m + r + 1) * lowerCharPiece q m x (r + 1))) := by
  refine isZDelta_zvar_mul_lowerCharPiece_of_isZDelta q hx.le_length r ?_
  have hb : ∀ b : Fin (m + 1), lowerTuple m r b ≠ m + r + 1 := by
    intro b
    induction b using Fin.lastCases with
    | last => rw [lowerTuple_last]; omega
    | cast j =>
      rw [lowerTuple_castSucc]
      have hj := j.isLt
      omega
  have h := isZDelta_auxToFrac_unnormalisedCharSeries (r := r) q hx (lowerTuple_injective m r)
    ⟨Fin.last m, lowerTuple_last m r⟩ fun a b _ hbb => absurd hbb (hb b)
  rwa [transposeTuple_lowerTuple] at h

end HJO.Dyck
