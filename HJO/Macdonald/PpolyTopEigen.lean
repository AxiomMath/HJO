/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.PpolyTop
public import HJO.Macdonald.SplitNumFactor
public import HJO.Macdonald.SplitShift

/-! # The summands of `macOpNum`, read in the greatest variable

Step 3 of the proof of `HJO.Mac.coeff_partExp_splitAt_macPpoly_eq` takes the coefficient of
`x_t^{n-1+r}` on both sides of the polynomial operator identity
`HJO.Mac.macOpNum_eq_vandermondeProd_mul`. On the left that means reading each summand of
`HJO.Mac.macOpNum`, and this file does that, one summand at a time.

A summand at the letter `i` is `(-1)^{c_i}·𝒱_{N∖{i}}·(∏_{j ≠ i}(u x_i - x_j))·T_{q,x_i}f`, and the
sign is left outside: what is proved here is the coefficient of the three-factor product
`𝒱_{N∖{i}}·A_i·T_{q,x_i}f`, so that the assembly can handle every sign in one place.

The two cases are genuinely different, and the degrees are what distinguish them:

* at `i = t` the Vandermonde factor is a *constant* in `x_t` — it does not mention `x_t` at all —
  and the numerator factor carries the whole degree `n-1`, contributing `u^{n-1}`;
* at `i ≠ t` the Vandermonde factor carries degree `n-2` and the numerator factor carries the
  remaining `1`.

Both add to `n-1`, which is why one index `Fintype.card {b // b ≠ t} + r` reads both. At `i ≠ t`
the index is written `(#(univ.erase ⟨i,_⟩) + 1) + r` before being split, and
`Finset.card_erase_add_one` turns it back; this is how `n-2` and `n-1` are kept apart with no
truncated subtraction anywhere.

Note that the `i = t` case needs no `IsTop t`: `univ.erase t` is the image of the small alphabet
whatever `t` is. Only the `i ≠ t` case does, through the Vandermonde split.

## The shift does not change the degree in `x_t`

A `q`-shift is invertible, so it cannot raise the degree in `x_t`. Both statements are read off the
coefficient laws of `HJO/Macdonald/SplitShift.lean`: the coefficient of `x_t^k` after the shift
is a unit multiple — respectively an automorphism image — of the coefficient before it, so it
vanishes exactly when that one does.

## Main results

* `HJO.Mac.natDegree_splitAt_rescaleEquiv_self_le`,
  `HJO.Mac.natDegree_splitAt_rescaleEquiv_of_ne_le`.
* `HJO.Mac.coeff_splitAt_numTerm_top`: the summand at the split letter.
* `HJO.Mac.coeff_splitAt_numTerm`: the summand at any other letter.

## References

This file supplies Step 3 of the proof of `HJO.Mac.coeff_partExp_splitAt_macPpoly_eq`, on
`HJO.Mac.vandermondeProd_mul_macOp`.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Mac

/-! ### The `q`-shift does not raise the degree in `x_t` -/

section Shift

variable {σ K : Type*} [Field K] [LinearOrder σ] {t : σ}

/-- The shift at the split letter multiplies the coefficient of `x_t^k` by the unit `q^k`, so it
cannot raise the degree in `x_t`. -/
theorem natDegree_splitAt_rescaleEquiv_self_le (q : Kˣ) (t : σ) (f : MvPolynomial σ K) {B : ℕ}
    (h : (splitAt t f).natDegree ≤ B) :
    (splitAt t (rescaleEquiv (Pi.mulSingle t q) f)).natDegree ≤ B :=
  Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun k hk => by
    rw [coeff_splitAt_rescaleEquiv_self, Polynomial.coeff_eq_zero_of_natDegree_lt (h.trans_lt hk),
      smul_zero]

/-- The shift at another letter acts on the coefficient of `x_t^k` by an automorphism, so it cannot
raise the degree in `x_t`. -/
theorem natDegree_splitAt_rescaleEquiv_of_ne_le (q : Kˣ) {i : σ} (hi : i ≠ t)
    (f : MvPolynomial σ K) {B : ℕ} (h : (splitAt t f).natDegree ≤ B) :
    (splitAt t (rescaleEquiv (Pi.mulSingle i q) f)).natDegree ≤ B :=
  Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun k hk => by
    rw [coeff_splitAt_rescaleEquiv_of_ne _ hi,
      Polynomial.coeff_eq_zero_of_natDegree_lt (h.trans_lt hk), map_zero]

end Shift

/-! ### The summands of `macOpNum` -/

section Term

variable {σ K : Type*} [Field K] [LinearOrder σ] [Fintype σ] {t : σ}

/-- **The summand of `macOpNum` at `i = t`, read at `x_t^{n-1+r}`** (sign excluded). The Vandermonde
factor is a constant in `x_t`, so the numerator factor carries the whole degree `n-1` and
contributes `u^{n-1}`; the shift contributes `q^r` on the coefficient of `x_t^r`. -/
theorem coeff_splitAt_numTerm_top (q : Kˣ) (u : K) {f : MvPolynomial σ K} {r : ℕ}
    (hf : (splitAt t f).natDegree ≤ r) :
    Polynomial.coeff (splitAt t (((univ : Finset σ).erase t).vandermondeProd X *
        (∏ j ∈ (univ : Finset σ).erase t, (C u * X t - X j)) *
        rescaleEquiv (Pi.mulSingle t q) f)) (Fintype.card {b : σ // b ≠ t} + r)
      = (univ : Finset {b : σ // b ≠ t}).vandermondeProd X *
          C u ^ Fintype.card {b : σ // b ≠ t} *
          ((q : K) ^ r • Polynomial.coeff (splitAt t f) r) := by
  have hV : splitAt t (((univ : Finset σ).erase t).vandermondeProd (X : σ → MvPolynomial σ K))
      = Polynomial.C ((univ : Finset {b : σ // b ≠ t}).vandermondeProd X) := by
    rw [univ_erase_top_eq_image t, splitAt_vandermondeProd_image]
  have hVA : (splitAt t (((univ : Finset σ).erase t).vandermondeProd X *
      (∏ j ∈ (univ : Finset σ).erase t, (C u * X t - X j)))).natDegree
        ≤ Fintype.card {b : σ // b ≠ t} := by
    rw [map_mul, hV]
    refine Polynomial.natDegree_mul_le.trans ?_
    rw [Polynomial.natDegree_C, zero_add]
    exact natDegree_splitAt_prod_numFactor_top_le u t
  rw [map_mul, Polynomial.coeff_mul_add_eq_of_natDegree_le hVA
      (natDegree_splitAt_rescaleEquiv_self_le q t f hf),
    map_mul, hV, Polynomial.coeff_C_mul, coeff_splitAt_prod_numFactor_top,
    coeff_splitAt_rescaleEquiv_self]

/-- **The summand of `macOpNum` at `i ≠ t`, read at `x_t^{n-1+r}`** (sign excluded). The Vandermonde
factor carries degree `n-2` with `(-1)^{n-2}𝒱_{N'∖{i}}`, the numerator factor carries the remaining
`1` with `-∏_{j ≠ i, j ≠ t}(u x_i - x_j)`, and the shift acts on the coefficient of `x_t^r` by the
rescaling of the small alphabet at `⟨i, _⟩`. -/
theorem coeff_splitAt_numTerm (ht : IsTop t) (q : Kˣ) (u : K) {i : σ} (hi : i ≠ t)
    {f : MvPolynomial σ K} {r : ℕ} (hf : (splitAt t f).natDegree ≤ r) :
    Polynomial.coeff (splitAt t (((univ : Finset σ).erase i).vandermondeProd X *
        (∏ j ∈ (univ : Finset σ).erase i, (C u * X i - X j)) *
        rescaleEquiv (Pi.mulSingle i q) f)) (Fintype.card {b : σ // b ≠ t} + r)
      = (-1) ^ ((univ : Finset {b : σ // b ≠ t}).erase ⟨i, hi⟩).card *
          ((univ : Finset {b : σ // b ≠ t}).erase ⟨i, hi⟩).vandermondeProd X *
          (-∏ c ∈ (univ : Finset {b : σ // b ≠ t}).erase ⟨i, hi⟩,
              (C u * X (⟨i, hi⟩ : {b : σ // b ≠ t}) - X c)) *
          rescaleEquiv (Pi.mulSingle (⟨i, hi⟩ : {b : σ // b ≠ t}) q)
            (Polynomial.coeff (splitAt t f) r) := by
  have hcard : ((univ : Finset {b : σ // b ≠ t}).erase ⟨i, hi⟩).card + 1
      = Fintype.card {b : σ // b ≠ t} := by
    rw [Finset.card_erase_add_one (Finset.mem_univ _), Finset.card_univ]
  have hVdeg : (splitAt t (((univ : Finset σ).erase i).vandermondeProd
      (X : σ → MvPolynomial σ K))).natDegree
      = ((univ : Finset {b : σ // b ≠ t}).erase ⟨i, hi⟩).card :=
    natDegree_splitAt_vandermondeProd_erase ht hi
  have hlead := leadingCoeff_splitAt_vandermondeProd_erase (K := K) ht hi
  rw [Polynomial.leadingCoeff, hVdeg] at hlead
  have hVA : (splitAt t (((univ : Finset σ).erase i).vandermondeProd X *
      (∏ j ∈ (univ : Finset σ).erase i, (C u * X i - X j)))).natDegree
        ≤ ((univ : Finset {b : σ // b ≠ t}).erase ⟨i, hi⟩).card + 1 := by
    rw [map_mul]
    exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add hVdeg.le (natDegree_splitAt_prod_numFactor_le u hi))
  rw [← hcard, map_mul,
    Polynomial.coeff_mul_add_eq_of_natDegree_le hVA
      (natDegree_splitAt_rescaleEquiv_of_ne_le q hi f hf),
    map_mul,
    Polynomial.coeff_mul_add_eq_of_natDegree_le hVdeg.le
      (natDegree_splitAt_prod_numFactor_le u hi),
    hlead, coeff_splitAt_prod_numFactor, coeff_splitAt_rescaleEquiv_of_ne]

end Term

end HJO.Mac

/-! ### The partition with its first row removed, and the eigenvalue it carries -/

namespace HJO.Sym

/-- **`λ` with its first row removed**: the partition `κ`, with `κ_i = λ_{i+1}`. Built through
`HJO.Sym.ofRowLenSeq` from the shifted row-length sequence — which is still weakly decreasing, and
still eventually zero because a row can only be nonempty when the row above it is. There is no row
removal on `YoungDiagram` in Mathlib, and `Nat.Partition.partitionWithPartEquiv` erases a part from
the *multiset* rather than shifting the sequence, so this is the construction the partition
`κ` needs. -/
noncomputable def shiftRows (Y : YoungDiagram) : YoungDiagram :=
  ofRowLenSeq (fun k => Y.rowLen (k + 1)) (fun _ _ hab => Y.rowLen_anti _ _ (by omega))
    ((rowLenSeq_finite_support Y).subset fun i hi => by
      have h1 : Y.rowLen (i + 1) ≤ Y.rowLen i := Y.rowLen_anti i (i + 1) (by omega)
      simp only [Set.mem_ofPred_eq, rowLenSeq_apply] at hi ⊢
      omega)

@[simp]
theorem rowLen_shiftRows (Y : YoungDiagram) (k : ℕ) :
    (shiftRows Y).rowLen k = Y.rowLen (k + 1) :=
  rowLen_ofRowLenSeq k

/-- **The eigenvalue split: `E_{n+1}(λ) = q^{λ_1}u^n + E_n(κ)`.** The `i = 0` term of
`E_{n+1}` is `q^{λ_1}u^n`, and reindexing the rest by `i = k+1` turns it into `E_n` of the shifted
partition — the exponent `(n+1)-1-(k+1)` being `n-1-k`.

Note this peels the *first* row, whereas `HJO.Sym.macdonaldEigenvalue_succ` peels the last. Step 3
of `HJO.Mac.coeff_partExp_splitAt_macPpoly_eq` needs the first: `q^{λ_1}u^{n-1}` is exactly what the
`i = t` summand of `macOpNum` contributes, and what is left over has to be the eigenvalue at `κ`. -/
theorem macdonaldEigenvalue_succ_peel {K : Type*} [CommRing K] (q u : K) (n : ℕ)
    (Y : YoungDiagram) :
    macdonaldEigenvalue q u (n + 1) Y
      = q ^ Y.rowLen 0 * u ^ n + macdonaldEigenvalue q u n (shiftRows Y) := by
  rw [macdonaldEigenvalue, macdonaldEigenvalue, Finset.sum_range_succ', add_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [rowLen_shiftRows]
  congr 2
  omega

end HJO.Sym

end
