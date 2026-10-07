/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.QShiftNegBraid
public meta import HJO.Attr

/-! # The lowering operator commutes with a braid operator it does not reach

`HJO.Sweep.dminusCM_braid`: for `k ≥ 3`, `1 ≤ i ≤ k-2` and `F ∈ V_k`,
`T_i(d_-F) = d_-(T_iF)`.

## The shape of the proof

`d_-` is the composite of the substitution `τ^-_{k,k}` with the coefficient extraction
`HJO.Sweep.lowerCoeffShift` at the index of the last variable `y_k`, and the two halves are
discharged separately.

* The substitution half is already proved: `HJO.Sweep.qshiftNeg_braid`, whose side condition
  `k ∉ {i, i+1}` is exactly `i ≤ k-2`.
* The extraction half is this file. `T_i` moves only `y_i` and `y_{i+1}`, and the extraction reads
  only `y_k`, so they commute as soon as `i + 1 ≤ k - 1`.

The extraction half is proved from two facts about `HJO.Sweep.lowerCoeffShift`, one for each summand
of `T_i = s_i + (q-1)y_i∂_i`:

* it commutes with `s_i`, because `s_i` permutes the `y`-monomial basis by a permutation fixing the
  extraction's own index (`HJO.Sweep.lowerCoeffShift_swapAux`);
* it is linear over the variables the extraction does not read, which is
  `HJO.Sweep.lowerCoeffShift_mul_of_mem_piece`, and that plus `HJO.Sweep.dividedDiff_unique` gives
  the divided difference.

The last two steps are packaged as `HJO.Sweep.dividedDiff_comm_of` and `HJO.Sweep.braid_comm_of`,
stated for an arbitrary `Λ`-linear operator with those two properties. Doing so costs nothing and
serves both lowering operators: `HJO.Sweep.dminusCM` (built on
`HJO.Sweep.lowerCoeffShift`) and its modified companion `HJO.Sweep.dminus`
(built on `HJO.Sweep.lowerCoeff`). The modified one is the operator
`HJO.Sweep.zopOneStar` reads, so both are needed downstream.

## The index range is exact

Stated on `V_{k+2}`, where the `1 ≤ i ≤ k-2` is `1 ≤ i ≤ k` and no subtraction is
truncated. At `i = k + 1` — the `i = k - 1`, the largest index `T_i` is defined at on
`V_k` — the statement is false: `T_{k+1}` moves `y_{k+2}`, the very variable the extraction reads.
So the upper bound is not slack.

Two of the hypotheses are dropped. `F ∈ V_k` is used by neither half — both hold on the
total space — and `1 ≤ i` is not used either, because `T_0` is the identity; the same two drops
`HJO.Sweep.qshiftNeg_braid` and `HJO.Sweep.braid_mul_mem_supported` already make. Nothing is
weakened.

## Main results

* `HJO.Sweep.dminusCM_braid`, `HJO.Sweep.dminusCM_mul_braidEnd`: `d_-T_i = T_id_-` on `V_{k+2}`
  for `i ≤ k`.
* `HJO.Sweep.dminus_braid`, `HJO.Sweep.dminus_mul_braidEnd`: the same for the modified operator
  `d^♭_-` of `HJO.Sweep.dminus`.

## References

Transcribing
E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, §5.
-/

@[expose] public section

namespace HJO.Sweep

section CommRingBase

variable {L : Type*} [CommRing L]

/-- `s_i` on a `y`-monomial: it transports the exponent vector along the transposition of the two
indices it swaps. -/
theorem swapAux_monomial (i : ℕ) (d : ℕ →₀ ℕ) (a : Sym.Lambda L) :
    swapAux L i (MvPolynomial.monomial d a)
      = MvPolynomial.monomial (Finsupp.mapDomain (Equiv.swap (i - 1) i) d) a := by
  rw [swapAux, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_monomial]

end CommRingBase

/-! ### A permutation fixing the read index passes the coefficient extraction -/

section Extraction

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- An equivalence fixing `j` leaves the exponent at `j` alone when it transports an exponent
vector. -/
theorem mapDomain_apply_of_apply_eq {e : ℕ ≃ ℕ} {j : ℕ} (he : e j = j) (d : ℕ →₀ ℕ) :
    Finsupp.mapDomain e d j = d j := by
  rw [← Finsupp.equivMapDomain_eq_mapDomain, Finsupp.equivMapDomain_apply,
    (Equiv.symm_apply_eq e).2 he.symm]

/-- An equivalence fixing `j` commutes with erasing the exponent at `j`. -/
theorem erase_mapDomain_of_apply_eq {e : ℕ ≃ ℕ} {j : ℕ} (he : e j = j) (d : ℕ →₀ ℕ) :
    Finsupp.erase j (Finsupp.mapDomain e d) = Finsupp.mapDomain e (Finsupp.erase j d) := by
  have hsymm : e.symm j = j := (Equiv.symm_apply_eq e).2 he.symm
  rw [← Finsupp.equivMapDomain_eq_mapDomain, ← Finsupp.equivMapDomain_eq_mapDomain]
  refine Finsupp.ext fun a => ?_
  by_cases ha : a = j
  · subst ha
    rw [Finsupp.erase_same, Finsupp.equivMapDomain_apply, hsymm, Finsupp.erase_same]
  · refine (Finsupp.erase_ne ha).trans ?_
    rw [Finsupp.equivMapDomain_apply, Finsupp.equivMapDomain_apply, Finsupp.erase_ne]
    intro hc
    rw [← hsymm] at hc
    exact ha (e.symm.injective hc)

/-- **`s_i` passes the coefficient extraction of `d_-`** when it does not touch the variable the
extraction reads: for `j ∉ {i-1, i}`, `s_i` permutes the `y`-monomial basis by a permutation fixing
the index `j`, so it commutes with `HJO.Sweep.lowerCoeffShift` at `j`. -/
theorem lowerCoeffShift_swapAux {i j : ℕ} (h1 : i - 1 ≠ j) (h2 : i ≠ j) (F : Total L) :
    lowerCoeffShift L j (swapAux L i F) = swapAux L i (lowerCoeffShift L j F) := by
  have he : Equiv.swap (i - 1) i j = j := Equiv.swap_apply_of_ne_of_ne (Ne.symm h1) (Ne.symm h2)
  induction F using MvPolynomial.induction_on' with
  | monomial d a =>
    rw [swapAux_monomial, lowerCoeffShift_monomial', lowerCoeffShift_monomial',
      mapDomain_apply_of_apply_eq he, erase_mapDomain_of_apply_eq he]
    simp only [map_mul, map_pow, map_neg, map_one, swapAux_C, swapAux_monomial]
  | add p r hp hr => rw [map_add, map_add, map_add, map_add, hp, hr]

/-- **`s_i` passes the coefficient extraction of the modified `d^♭_-`**, the same statement for
`HJO.Sweep.lowerCoeff`. -/
theorem lowerCoeff_swapAux {i j : ℕ} (h1 : i - 1 ≠ j) (h2 : i ≠ j) (F : Total L) :
    lowerCoeff L j (swapAux L i F) = swapAux L i (lowerCoeff L j F) := by
  have he : Equiv.swap (i - 1) i j = j := Equiv.swap_apply_of_ne_of_ne (Ne.symm h1) (Ne.symm h2)
  induction F using MvPolynomial.induction_on' with
  | monomial d a =>
    rw [swapAux_monomial, lowerCoeff_monomial', lowerCoeff_monomial',
      mapDomain_apply_of_apply_eq he, erase_mapDomain_of_apply_eq he]
    simp only [map_mul, map_pow, map_neg, map_one, swapAux_C, swapAux_monomial]
  | add p r hp hr => rw [map_add, map_add, map_add, map_add, hp, hr]

end Extraction

/-! ### A `Λ`-linear operator that passes `s_i` and the two variables passes `T_i` -/

section Comm

variable {L : Type*} [Field L]

/-- A `Λ`-linear operator commuting with `s_i` and with multiplication by the two variables `s_i`
moves commutes with `∂_i`.

The quotient that `HJO.Sweep.dividedDiff_unique` pins is `E(∂_iF)`, because multiplying it by
`y_{i+1} - y_i` pushes the factor inside `E` and turns it into `E(F - s_iF)`. -/
theorem dividedDiff_comm_of {i : ℕ} (E : Total L →ₗ[Sym.Lambda L] Total L)
    (hswap : ∀ F, E (swapAux L i F) = swapAux L i (E F))
    (hX : ∀ n, n = i - 1 ∨ n = i → ∀ G, E ((MvPolynomial.X n : Total L) * G)
      = MvPolynomial.X n * E G) (F : Total L) :
    E (dividedDiff i F) = dividedDiff i (E F) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [dividedDiff_zero_index, dividedDiff_zero_index, map_zero]
  have hD : ∀ G : Total L,
      E ((MvPolynomial.X i - MvPolynomial.X (i - 1) : Total L) * G)
        = (MvPolynomial.X i - MvPolynomial.X (i - 1) : Total L) * E G := fun G => by
    rw [sub_mul, map_sub, hX i (Or.inr rfl), hX (i - 1) (Or.inl rfl), sub_mul]
  refine dividedDiff_unique hi ?_
  rw [← hD, dividedDiff_spec, map_sub, hswap]

/-- A `Λ`-linear operator commuting with `s_i` and with multiplication by the two variables `s_i`
moves commutes with `T_i`: the first summand of `T_iF = s_iF + (q-1)y_i∂_iF` is the hypothesis, and
the second is `HJO.Sweep.dividedDiff_comm_of` together with the scalar and `y_i` passing `E`. -/
theorem braid_comm_of (q : L) {i : ℕ} (E : Total L →ₗ[Sym.Lambda L] Total L)
    (hswap : ∀ F, E (swapAux L i F) = swapAux L i (E F))
    (hX : ∀ n, n = i - 1 ∨ n = i → ∀ G, E ((MvPolynomial.X n : Total L) * G)
      = MvPolynomial.X n * E G) (F : Total L) :
    E (braid q i F) = braid q i (E F) := by
  have hC : ∀ (c : Sym.Lambda L) (G : Total L),
      E (MvPolynomial.C c * G) = MvPolynomial.C c * E G := fun c G => by
    rw [← MvPolynomial.smul_eq_C_mul, map_smul, MvPolynomial.smul_eq_C_mul]
  have hscal : ∀ (x : L) (G : Total L), E (scal x * G) = scal x * E G := fun x G => by
    have hx : (scal x : Total L) = MvPolynomial.C (MvPolynomial.C x) := rfl
    rw [hx, hC]
  rw [braid_apply, braid_apply, map_add, hswap, mul_assoc, mul_assoc, hscal, auxVar,
    hX (i - 1) (Or.inl rfl), dividedDiff_comm_of E hswap hX]

end Comm

/-! ### The two lowering operators against a distant braid operator -/

section Newton

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The coefficient extraction of `d_-` commutes with a braid operator below it**: for `i < j`,
`T_i` moves only `y_i, y_{i+1}` while the extraction reads `y_{j+1}`. -/
theorem lowerCoeffShift_braid (q : L) {i j : ℕ} (hij : i < j) (F : Total L) :
    lowerCoeffShift L j (braid q i F) = braid q i (lowerCoeffShift L j F) :=
  braid_comm_of q _ (fun F => lowerCoeffShift_swapAux (by omega) (by omega) F)
    (fun n hn G => by
      rcases hn with rfl | rfl
      · exact lowerCoeffShift_mul_of_mem_piece (X_mem_piece (by omega)) G
      · exact lowerCoeffShift_mul_of_mem_piece (X_mem_piece (by omega)) G) F

/-- **The coefficient extraction of `d^♭_-` commutes with a braid operator below it.** -/
theorem lowerCoeff_braid (q : L) {i j : ℕ} (hij : i < j) (F : Total L) :
    lowerCoeff L j (braid q i F) = braid q i (lowerCoeff L j F) :=
  braid_comm_of q _ (fun F => lowerCoeff_swapAux (by omega) (by omega) F)
    (fun n hn G => by
      rcases hn with rfl | rfl
      · exact lowerCoeff_mul_of_mem_piece (X_mem_piece (by omega)) G
      · exact lowerCoeff_mul_of_mem_piece (X_mem_piece (by omega)) G) F

/-- **The lowering operator commutes with the braid operators.** This is
`HJO.Sweep.dminusCM_braid`: `T_i(d_-F) = d_-(T_iF)` for `1 ≤ i ≤ k-2`, with `d_-` the operator of
`HJO.Sweep.dminusCM`.

Stated on `V_{k+2}`, where the `1 ≤ i ≤ k-2` reads `1 ≤ i ≤ k` and no subtraction is
truncated. The substitution half is `HJO.Sweep.qshiftNeg_braid` and the extraction half is
`HJO.Sweep.lowerCoeffShift_braid`; the hypothesis `F ∈ V_k` is used by neither and is
dropped, as is its `1 ≤ i` — at the unread index `0` the statement still holds, `T_0` being the
identity. -/
@[hjo "lem_cm_rel_dminus_braid"]
theorem dminusCM_braid (q : L) {k i : ℕ} (hik : i ≤ k) (F : Total L) :
    dminusCM q (k + 2) (braid q i F) = braid q i (dminusCM q (k + 2) F) := by
  rw [dminusCM_succ_apply, dminusCM_succ_apply,
    qshiftNeg_braid q (by omega) (by omega) (by omega), lowerCoeffShift_braid q (by omega)]

/-- `HJO.Sweep.dminusCM_braid` in the endomorphism monoid: `d_-T_i = T_id_-` for `1 ≤ i ≤ k`, read
on `V_{k+2}`. This is the form the `z`-relations of `HJO.Sweep.zop` consume. -/
theorem dminusCM_mul_braidEnd (q : L) {k i : ℕ} (hik : i ≤ k) :
    dminusCM q (k + 2) * braidEnd q i = braidEnd q i * dminusCM q (k + 2) :=
  LinearMap.ext fun F => dminusCM_braid q hik F

/-- **The modified lowering operator commutes with the braid operators**: `HJO.Sweep.dminusCM_braid`
for the `d^♭_-` of `HJO.Sweep.dminus`, at the same index range and by the same two halves. The
lemma is stated only for `HJO.Sweep.dminusCM`, but `HJO.Sweep.zopOneStar` — the `z_1` of
`HJO.Sweep.zop` — is written with the modified operator, so this is the form needed there. -/
theorem dminus_braid (q : L) {k i : ℕ} (hik : i ≤ k) (F : Total L) :
    dminus q (k + 2) (braid q i F) = braid q i (dminus q (k + 2) F) := by
  rw [dminus_succ_apply, dminus_succ_apply, qshiftNeg_braid q (by omega) (by omega) (by omega),
    lowerCoeff_braid q (by omega)]

/-- `HJO.Sweep.dminus_braid` in the endomorphism monoid. -/
theorem dminus_mul_braidEnd (q : L) {k i : ℕ} (hik : i ≤ k) :
    dminus q (k + 2) * braidEnd q i = braidEnd q i * dminus q (k + 2) :=
  LinearMap.ext fun F => dminus_braid q hik F

end Newton

end HJO.Sweep
