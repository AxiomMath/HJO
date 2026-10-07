/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.Completion
public import HJO.Collinear.EsymmAlphabet
public import HJO.PlethysticAlphabet
public import HJO.Macdonald.DopZeroHtilde
public meta import HJO.Attr

/-! # The shift of a basic operator

The last of the four propositions of Mellit's Section 3.7, `HJO.Sym.nsShiftComp_comp_dopInt`:
`τ^*τ(-D_{n+1}) = D̂_n τ^*τ`. Mellit (*Toric braids and `(m, n)`-parking functions*,
arXiv:1604.07456, §3.7) says only "by a direct calculation"; this file spells that calculation out.

## The two halves

Writing `g = τf = f[X+1]`, the generating object `F(z) = f[X+1+M/z]·Exp[-zX]` has
`[z^k]F = D_k(g)` by `HJO.Sym.DopInt`, so the calculation is two statements about `D` and one
assembly:

* **Conjugating `D` by `τ`.** `HJO.Sym.unitShift_dop` — `τD_{n+1}τ^{-1} = D_{n+1} - D_n`, which is
  the `(D_{n+1}f)[X+1] = [z^{n+1}]F - [z^n]F`. It rests on `e_r[X+1] = e_r + e_{r-1}`
  (`HJO.Sym.unitShift_elemSymm`), the single-letter case of the convolution
  `HJO.Bglx.map_elemSymm_add`, which is the coefficient form of
  `Exp[-z(X+1)] = Exp[-zX](1-z)`.
* **`D` past a factor of `Exp[-X/M]`.** `HJO.Sym.dop_mul_expNegDivM` —
  `D_n(A·h_{m+1}[-X/M]) = h_{m+1}[-X/M]·D_nA - h_m[-X/M]·D_{n+1}A`, the coefficient form of
  `Exp[-(X+M/z)/M] = Exp[-X/M]·(1 - z^{-1})`. It is
  `HJO.Sym.completeHomog_add_alphabet` at the splitting
  `p_k ↦ -p_k/M_k` plus `p_k ↦ -z^{-k}`, whose second half kills `h_s` for `s ≥ 2`
  (`HJO.Sym.completeHomog_neg_letter_eq_zero`).

## Main results

* `HJO.Sym.nsShiftComp_comp_dopInt` — the main result: `τ^*τ(-D_{n+1}) = D̂_n τ^*τ` for every
  `n ∈ ℤ`.
* `HJO.Sym.unitShift_dopInt` and `HJO.Sym.dopInt_mul_expNegDivM` — the two halves above.
* `HJO.Sym.sum_extVal_mul` — the index bookkeeping the assembly needs: the members of `D̂` paired
  off against a family over `range (e+1)` are `D` of the members themselves over `range (m+1)`,
  where `m + c = e`.

## The hypothesis the main result acquires

`dopInt_mul_expNegDivM` needs `(1-q^k)(1-u^k) ≠ 0` for every `k ≥ 1` — it is where the displaced
alphabet `-(X + M/z)/M` splits, and the splitting uses `M_k⁻¹·M_k = 1`. Nothing else in the chain
reads it: `HJO.Sym.nsShiftStar` and `HJO.Sym.nsShiftComp_injective` got by on `h_0 = 1` alone. So
the main result carries `hM`, which is the nondegeneracy `HJO.Sym.eq_plethNegDivM` asks of the
parameters and which the `𝕜` discharges by algebraic independence.

## Index range

`HJO.Sym.DopInt` is stated for `k ∈ ℤ`, the negative indices being there because the shift
identities quantify over all of `ℤ` — `HJO.Sym.nsShiftComp_comp_dopInt` is such an identity, at
`D_{n+1}` and `D̂_n` for every `n ∈ ℤ`. `HJO.Sym.Dop` is indexed by `ℕ`, so it cannot state the
main result. `HJO.Sym.DopInt` here is the operator at an integer index,
agreeing with `Dop` at a natural one (`HJO.Sym.dopInt_natCast`): the extraction `[z^k]` drops the
terms whose elementary symmetric function would have a negative index, which for `k ≥ 0` is no term
at all.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Sym

section Field

variable {K : Type*} [Field K] [Algebra ℚ K]

/-! ### `e_r[X+1] = e_r + e_{r-1}` -/

/-- The one-letter alphabet `1`: the `𝕜`-algebra endomorphism of `Λ` with `p_j ↦ 1`. It is the
second summand of `τ`, whose prescription is `p_j ↦ p_j + 1`. -/
noncomputable def oneLetter (K : Type*) [CommRing K] : Lambda K →ₐ[K] Lambda K :=
  MvPolynomial.aeval fun _ => 1

omit [Algebra ℚ K] in
theorem oneLetter_powerSum (j : ℕ) : oneLetter K (powerSum K j) = 1 ^ j := by
  rw [one_pow, powerSum, oneLetter, MvPolynomial.aeval_X]

/-- **`e_r[X+1] = e_r + e_{r-1}`.** The elementary symmetric functions of `X` with the single letter
`1` adjoined: `HJO.Bglx.map_elemSymm_add` convolves them against those of the one-letter alphabet,
and `HJO.Bglx.map_elemSymm_geom` says the latter are `1, 1, 0, 0, …`, so only the top two terms of
the convolution survive.

This is the coefficient form of the `Exp[-z(X+1)] = Exp[-zX]·(1-z)`: comparing the
coefficient of `z^r` in `∑_r (-z)^r e_r[X+1] = (1-z)∑_r(-z)^r e_r` gives exactly this. -/
theorem unitShift_elemSymm (r : ℕ) :
    unitShift (elemSymm K (r + 1)) = elemSymm K (r + 1) + elemSymm K r := by
  have hsplit : ∀ j : ℕ, 1 ≤ j → unitShift (powerSum K j)
      = (AlgHom.id K (Lambda K)) (powerSum K j) + oneLetter K (powerSum K j) := by
    intro j hj
    rw [unitShift_powerSum hj, AlgHom.id_apply, oneLetter_powerSum j, one_pow]
  have hconv := Bglx.map_elemSymm_add (AlgHom.id K (Lambda K)) (oneLetter K) unitShift hsplit
    (r + 1)
  have hgeom : ∀ s : ℕ, oneLetter K (elemSymm K s) = if s = 0 then 1 else if s = 1 then 1 else 0 :=
    fun s => Bglx.map_elemSymm_geom 1 (oneLetter K) (fun j _ => oneLetter_powerSum j) s
  rw [hconv]
  rw [Finset.sum_eq_add_of_mem 0 1 (by simp) (by simp) (by omega) ?_]
  · rw [hgeom 0, hgeom 1]
    simp
  · intro s hs hs01
    rw [hgeom s]
    simp [hs01.1, hs01.2]


/-! ### The basic operator at an integer index -/

/-- The signed elementary symmetric function at an integer index: `(-1)^m e_m` for `m ≥ 0`, and
`0` below, which is the convention `HJO.Sym.DopInt` reads when it allows a negative extraction
index. -/
noncomputable def esymmSigned (K : Type*) [CommRing K] [Algebra ℚ K] (m : ℤ) : Lambda K :=
  if 0 ≤ m then (-1) ^ m.toNat * elemSymm K m.toNat else 0

theorem esymmSigned_natCast (m : ℕ) :
    esymmSigned K (m : ℤ) = (-1) ^ m * elemSymm K m := by
  rw [esymmSigned, Int.toNat_natCast]
  split_ifs with h
  · rfl
  · exact absurd (Int.natCast_nonneg m) h

theorem esymmSigned_of_neg {m : ℤ} (hm : m < 0) : esymmSigned K m = 0 := by
  rw [esymmSigned]
  split_ifs with h
  · exact absurd h (by omega)
  · rfl

/-- **`τ` on the signed elementary symmetric functions**: `τ(c_m) = c_m - c_{m-1}`, which is
`e_r[X+1] = e_r + e_{r-1}` with the sign `(-1)^m` folded in. It holds at every integer index: at
`m = 0` the subtracted term is the one below the range and vanishes, and `e_0 = 1` is fixed.

This is the identity the conjugation of `HJO.Sym.DopInt` by `τ` runs on, and it is where the
factor `Exp[-z(X+1)] = Exp[-zX](1-z)` enters. -/
theorem unitShift_esymmSigned (m : ℤ) :
    unitShift (esymmSigned K m) = esymmSigned K m - esymmSigned K (m - 1) := by
  rcases lt_or_ge m 0 with hm | hm
  · rw [esymmSigned_of_neg hm, esymmSigned_of_neg (by omega), map_zero, sub_zero]
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, m = (r : ℤ) := ⟨m.toNat, (Int.toNat_of_nonneg hm).symm⟩
  match r with
  | 0 =>
    rw [esymmSigned_natCast, esymmSigned_of_neg (by omega), elemSymm_zero K]
    simp
  | r + 1 =>
    rw [esymmSigned_natCast, show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) from by push_cast; ring,
      esymmSigned_natCast, map_mul, map_pow, map_neg, map_one, unitShift_elemSymm]
    ring

/-- **The basic operator `D_k` at an integer index**, `HJO.Sym.DopInt` for `k ∈ ℤ`:
`D_k f = [z^k](f[X+M/z]·Exp[-zX])`, which pairs the coefficient of `w^j = z^{-j}` in `f[X+M/z]`
against `(-1)^{k+j}e_{k+j}`, read as `0` where the index is negative.

`HJO.Sym.Dop` is this at a natural index (`HJO.Sym.dopInt_natCast`). The integer index is
not decoration: `HJO.Sym.nsShiftComp_comp_dopInt` quantifies over all of `ℤ`, and that is why the
negative indices are admitted. -/
@[hjo "def_dop"]
noncomputable def DopInt (q u : K) (k : ℤ) : Module.End K (Lambda K) :=
  coeffPairing (fun j : ℕ => esymmSigned K (k + j)) ∘ₗ (plethShift q u).toLinearMap

theorem dopInt_natCast (q u : K) (k : ℕ) : DopInt q u (k : ℤ) = Dop q u k := by
  have hfam : (fun j : ℕ => esymmSigned K ((k : ℤ) + j))
      = fun j : ℕ => (-1 : Lambda K) ^ (k + j) * elemSymm K (k + j) := by
    refine funext fun j => ?_
    rw [show ((k : ℤ) + (j : ℤ)) = ((k + j : ℕ) : ℤ) from by push_cast; ring, esymmSigned_natCast]
  rw [DopInt, Dop, hfam]

/-- **`D_k` shifts degree by `k`**, `HJO.Sym.dop_shiftsDegree` at an integer index: the coefficient
of `w^j` lies in `Λ_{d-j}` and `c_{k+j}` in `Λ_{k+j}`, read as the zero subspace where the index is
negative. -/
theorem dopInt_shiftsDegree (q u : K) (k : ℤ) : ShiftsDegree k (DopInt q u k) := by
  intro d f hf
  change coeffPairing (fun j : ℕ => esymmSigned K (k + j)) (plethShift q u f) ∈ _
  refine coeffPairing_mem_lambdaCompInt (e := k) (fun j => ?_) (plethShift_mem_polyComp q u hf)
  rcases lt_or_ge (k + (j : ℤ)) 0 with hkj | hkj
  · rw [esymmSigned_of_neg hkj]
    exact zero_mem _
  · obtain ⟨p, hp⟩ : ∃ p : ℕ, k + (j : ℤ) = (p : ℤ) :=
      ⟨(k + (j : ℤ)).toNat, (Int.toNat_of_nonneg hkj).symm⟩
    rw [hp, esymmSigned_natCast, lambdaCompInt_natCast]
    have hsign : ((-1 : Lambda K) ^ p) ∈ LambdaComp K 0 := neg_one_pow_mem_lambdaComp K p
    have h := mul_mem_lambdaComp hsign (elemSymm_mem_lambdaComp K p)
    rwa [zero_add] at h

/-! ### Conjugating the basic operator by `τ` -/

omit [Algebra ℚ K] in
/-- `τ` fixes the constants, being an algebra map. -/
theorem unitShift_C (a : K) : unitShift (MvPolynomial.C a : Lambda K) = MvPolynomial.C a := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]

omit [Algebra ℚ K] in
/-- **`τ` commutes with the displacement**: `(τf)[X+M/z] = (f[X+M/z])[X+1]`, both being the algebra
map sending `p_k` to `p_k + 1 + M_k w^k`. -/
theorem plethShift_unitShift (q u : K) (f : Lambda K) :
    plethShift q u (unitShift f)
      = (plethShift q u f).map
        ((unitShift : Lambda K →ₐ[K] Lambda K) : Lambda K →+* Lambda K) := by
  have hext : (plethShift q u).comp (unitShift : Lambda K →ₐ[K] Lambda K)
      = (Polynomial.mapAlgHom (unitShift : Lambda K →ₐ[K] Lambda K)).comp (plethShift q u) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    have hXp : (MvPolynomial.X i : Lambda K) = powerSum K (i + 1) := by
      rw [powerSum, Nat.add_sub_cancel]
    have hL : ((plethShift q u).comp (unitShift : Lambda K →ₐ[K] Lambda K)) (MvPolynomial.X i)
        = plethShift q u (MvPolynomial.X i) + 1 := by
      rw [AlgHom.comp_apply, unitShift, MvPolynomial.aeval_X, map_add, map_one]
    have hR : ((Polynomial.mapAlgHom (unitShift : Lambda K →ₐ[K] Lambda K)).comp
          (plethShift q u)) (MvPolynomial.X i)
        = Polynomial.C (powerSum K (i + 1) + 1)
          + Polynomial.C (MvPolynomial.C ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1))))
            * Polynomial.X ^ (i + 1) := by
      rw [AlgHom.comp_apply, hXp, plethShift_powerSum q (by omega), Polynomial.coe_mapAlgHom,
        Polynomial.map_add,
        Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_C,
        Polynomial.map_X]
      simp only [RingHom.coe_coe]
      rw [unitShift_powerSum (Nat.succ_le_succ (Nat.zero_le i)), unitShift_C]
    rw [hL, hR, hXp, plethShift_powerSum q (by omega), Polynomial.C_add, Polynomial.C_1]
    ring
  exact DFunLike.congr_fun hext f

omit [Algebra ℚ K] in
theorem coeff_plethShift_unitShift (q u : K) (f : Lambda K) (j : ℕ) :
    (plethShift q u (unitShift f)).coeff j = unitShift ((plethShift q u f).coeff j) := by
  rw [plethShift_unitShift, Polynomial.coeff_map]
  rfl

/-- **Conjugating `D_k` by `τ`**, the `(D_{k}f)[X+1] = [z^{k}]F - [z^{k-1}]F`:
`τ(D_k f) = D_k(τf) - D_{k-1}(τf)`.

The displacement passes through `τ` (`HJO.Sym.plethShift_unitShift`), so the only thing `τ` meets is
the family `c_{k+j}`, on which it is `HJO.Sym.unitShift_esymmSigned`: `c_m ↦ c_m - c_{m-1}`. The
second half of that is the pairing at the index one lower, which is `D_{k-1}`. -/
theorem unitShift_dopInt (q u : K) (k : ℤ) (f : Lambda K) :
    unitShift (DopInt q u k f)
      = DopInt q u k (unitShift f) - DopInt q u (k - 1) (unitShift f) := by
  set P : Polynomial (Lambda K) := plethShift q u f with hP
  set P' : Polynomial (Lambda K) := plethShift q u (unitShift f) with hP'
  have hmap : P' = P.map ((unitShift : Lambda K →ₐ[K] Lambda K) : Lambda K →+* Lambda K) :=
    plethShift_unitShift q u f
  have hzero : ∀ j : ℕ, P.natDegree + 1 ≤ j → P.coeff j = 0 := fun j hj =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hzero' : ∀ j : ℕ, P.natDegree + 1 ≤ j → P'.coeff j = 0 := fun j hj => by
    rw [hmap, Polynomial.coeff_map, hzero j hj]
    exact map_zero _
  have hlhs : unitShift (DopInt q u k f)
      = ∑ j ∈ range (P.natDegree + 1),
          unitShift (P.coeff j) * unitShift (esymmSigned K (k + j)) := by
    change unitShift (coeffPairing (fun j : ℕ => esymmSigned K (k + j)) P) = _
    rw [coeffPairing_eq_sum_range _ _ hzero, map_sum]
    exact Finset.sum_congr rfl fun j _ => map_mul _ _ _
  have hcoe : ∀ j : ℕ, P'.coeff j = unitShift (P.coeff j) := fun j => by
    rw [hmap, Polynomial.coeff_map]; rfl
  rw [hlhs]
  have hr1 : DopInt q u k (unitShift f)
      = ∑ j ∈ range (P.natDegree + 1), unitShift (P.coeff j) * esymmSigned K (k + j) := by
    change coeffPairing (fun j : ℕ => esymmSigned K (k + j)) P' = _
    rw [coeffPairing_eq_sum_range _ _ hzero']
    exact Finset.sum_congr rfl fun j _ => by rw [hcoe j]
  have hr2 : DopInt q u (k - 1) (unitShift f)
      = ∑ j ∈ range (P.natDegree + 1), unitShift (P.coeff j) * esymmSigned K (k + j - 1) := by
    change coeffPairing (fun j : ℕ => esymmSigned K (k - 1 + j)) P' = _
    rw [coeffPairing_eq_sum_range _ _ hzero']
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcoe j, show k - 1 + (j : ℤ) = k + (j : ℤ) - 1 from by ring]
  rw [hr1, hr2, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by
    rw [unitShift_esymmSigned, mul_sub]


/-! ### Pushing the basic operator past a factor of `Exp[-X/M]` -/

/-- The alphabet `-1/z`: the `𝕜`-algebra map `Λ → Λ[w]` with `p_k ↦ -w^k`, the second summand of
the displaced alphabet `-(X + M/z)/M`. -/
noncomputable def negLetterW (K : Type*) [CommRing K] :
    Lambda K →ₐ[K] Polynomial (Lambda K) :=
  MvPolynomial.aeval fun i => -(Polynomial.X ^ (i + 1))

omit [Algebra ℚ K] in
theorem negLetterW_powerSum {j : ℕ} (hj : 1 ≤ j) :
    negLetterW K (powerSum K j) = -(Polynomial.X ^ j : Polynomial (Lambda K)) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [powerSum, negLetterW, Nat.add_sub_cancel, MvPolynomial.aeval_X]

/-- **`Exp[-1/z] = 1 - z^{-1}`**, in the only form the calculation reads it: the alphabet `-1/z` is
a negated single letter, so `h_s` of it vanishes for `s ≥ 2`
(`HJO.Sym.completeHomog_neg_letter_eq_zero`), leaving `h_0 = 1` and `h_1 = -w`. -/
theorem negLetterW_completeHomog (s : ℕ) :
    negLetterW K (completeHomog K s)
      = if s = 0 then 1 else if s = 1 then -(Polynomial.X : Polynomial (Lambda K)) else 0 := by
  match s with
  | 0 =>
    rw [CopPower.completeHomog_zero, map_one]
    simp
  | 1 =>
    rw [CopPower.completeHomog_one, negLetterW_powerSum le_rfl, pow_one]
    simp
  | s + 2 =>
    rw [completeHomog_neg_letter_eq_zero (negLetterW K) Polynomial.X
      (fun j hj => negLetterW_powerSum hj) (by omega)]
    simp

/-- **The displaced `Exp[-X/M]`**, the `Exp[-(X + M/z)/M] = Exp[-X/M]·(1 - z^{-1})`,
degree by degree: `h_{m+1}[-X/M]` displaced is `h_{m+1}[-X/M] - h_m[-X/M]·w`.

`HJO.Sym.completeHomog_add_alphabet` at the splitting `p_k ↦ -p_k/M_k` plus `p_k ↦ -w^k` of the
displaced alphabet: the first summand is the undisplaced substitution and the second is a negated
single letter, so the convolution has only its top two terms. **The splitting is where the
parameters must be nondegenerate**: it needs `M_k⁻¹·M_k = 1`, so `hM` is not decoration here, unlike
everywhere else `Exp[-X/M]` has occurred so far. -/
theorem plethShift_plethNegDivM_completeHomog (q u : K)
    (hM : ∀ k : ℕ, 1 ≤ k → (1 - q ^ k) * (1 - u ^ k) ≠ 0) (m : ℕ) :
    plethShift q u (plethNegDivM q u (completeHomog K (m + 1)))
      = Polynomial.C (plethNegDivM q u (completeHomog K (m + 1)))
        - Polynomial.C (plethNegDivM q u (completeHomog K m)) * Polynomial.X := by
  have hsplit : ∀ j : ℕ, 0 < j →
      ((plethShift q u : Lambda K →ₐ[K] Polynomial (Lambda K)) :
            Lambda K →+* Polynomial (Lambda K)).comp
          ((plethNegDivM q u : Lambda K →ₐ[K] Lambda K) : Lambda K →+* Lambda K)
            (powerSum K j)
        = ((Polynomial.C : Lambda K →+* Polynomial (Lambda K)).comp
            ((plethNegDivM q u : Lambda K →ₐ[K] Lambda K) : Lambda K →+* Lambda K))
              (powerSum K j)
          + negLetterW K (powerSum K j) := by
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hMj := hM (i + 1) (by omega)
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [plethNegDivM_powerSum q u (by omega), map_mul, plethShift_powerSum q (by omega),
      negLetterW_powerSum (by omega)]
    have hC : plethShift q u (MvPolynomial.C (-((1 - q ^ (i + 1)) * (1 - u ^ (i + 1)))⁻¹))
        = Polynomial.C (MvPolynomial.C (-((1 - q ^ (i + 1)) * (1 - u ^ (i + 1)))⁻¹)) := by
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
      rfl
    rw [hC, mul_add, ← Polynomial.C_mul, ← mul_assoc, ← Polynomial.C_mul, ← MvPolynomial.C_mul,
      neg_mul, inv_mul_cancel₀ hMj]
    simp
  have hconv := completeHomog_add_alphabet
    ((Polynomial.C : Lambda K →+* Polynomial (Lambda K)).comp
      ((plethNegDivM q u : Lambda K →ₐ[K] Lambda K) : Lambda K →+* Lambda K))
    (negLetterW K)
    (((plethShift q u : Lambda K →ₐ[K] Polynomial (Lambda K)) :
        Lambda K →+* Polynomial (Lambda K)).comp
      ((plethNegDivM q u : Lambda K →ₐ[K] Lambda K) : Lambda K →+* Lambda K))
    hsplit (m + 1)
  have h0 : negLetterW K (completeHomog K 0) = 1 := by
    rw [negLetterW_completeHomog]
    norm_num
  have h1 : negLetterW K (completeHomog K 1) = -(Polynomial.X : Polynomial (Lambda K)) := by
    rw [negLetterW_completeHomog]
    norm_num
  rw [Finset.sum_eq_add_of_mem 0 1 (by simp) (by simp) (by omega) ?_] at hconv
  · simp only [RingHom.comp_apply, RingHom.coe_coe, h0, h1, Nat.sub_zero,
      Nat.add_sub_cancel, mul_one] at hconv
    rw [hconv]
    ring
  · intro t ht ht01
    rw [negLetterW_completeHomog t]
    simp [ht01.1, ht01.2]

/-- **`D_n` past a factor of `Exp[-X/M]`**: `D_n(A·h_{m+1}[-X/M])` is
`h_{m+1}[-X/M]·D_nA - h_m[-X/M]·D_{n+1}A`.

The displaced factor is `C(B_{m+1}) - C(B_m)·w` by
`HJO.Sym.plethShift_plethNegDivM_completeHomog`, and a monomial factor pulled out of a pairing
takes its scalar outside and reads the family one place further along
(`HJO.Sym.coeffPairing_C_mul`, `HJO.Sym.coeffPairing_X_mul`) — one place further along is the
basic operator at the next index. -/
theorem dopInt_mul_expNegDivM (q u : K)
    (hM : ∀ k : ℕ, 1 ≤ k → (1 - q ^ k) * (1 - u ^ k) ≠ 0) (n : ℤ) (m : ℕ) (A : Lambda K) :
    DopInt q u n (A * plethNegDivM q u (completeHomog K (m + 1)))
      = plethNegDivM q u (completeHomog K (m + 1)) * DopInt q u n A
        - plethNegDivM q u (completeHomog K m) * DopInt q u (n + 1) A := by
  have hfam : (fun j : ℕ => esymmSigned K (n + (j + 1)))
      = fun j : ℕ => esymmSigned K (n + 1 + j) := by
    refine funext fun j => ?_
    rw [show n + ((j : ℤ) + 1) = n + 1 + (j : ℤ) from by ring]
  change coeffPairing (fun j : ℕ => esymmSigned K (n + j))
      (plethShift q u (A * plethNegDivM q u (completeHomog K (m + 1)))) = _
  rw [map_mul, plethShift_plethNegDivM_completeHomog q u hM m, mul_sub, map_sub]
  congr 1
  · rw [show plethShift q u A * Polynomial.C (plethNegDivM q u (completeHomog K (m + 1)))
        = Polynomial.C (plethNegDivM q u (completeHomog K (m + 1))) * plethShift q u A from
      mul_comm _ _, coeffPairing_C_mul]
    rfl
  · rw [show plethShift q u A * (Polynomial.C (plethNegDivM q u (completeHomog K m))
          * Polynomial.X)
        = Polynomial.C (plethNegDivM q u (completeHomog K m)) * (Polynomial.X
          * plethShift q u A) from by ring,
      coeffPairing_C_mul, coeffPairing_X_mul]
    congr 1
    change coeffPairing (fun j : ℕ => esymmSigned K (n + ((j : ℕ) + 1))) _ = _
    rw [hfam]
    rfl

/-- The degree-zero member is `1`, so `D_n` passes it untouched. -/
theorem dopInt_mul_expNegDivM_zero (q u : K) (n : ℤ) (A : Lambda K) :
    DopInt q u n (A * plethNegDivM q u (completeHomog K 0)) = DopInt q u n A := by
  rw [CopPower.completeHomog_zero, map_one, mul_one]


/-! ### The assembly -/

omit [Algebra ℚ K] in
/-- **Reindexing the members of an extension against a convolution.** The members of `D̂` are `D` of
the members of `F`, shifted by `c`, so pairing them off against a family over `range (e+1)` is
pairing off `D` of the members themselves over `range (m+1)`, where `m + c = e`. The terms the
shift adds at one end are zero: at `c ≥ 0` because the extension has no member below `c`, at
`c < 0` because `D` carries `Λ_d` into `Λ_{d+c}`, which is the zero subspace for `d < -c`. -/
theorem sum_extVal_mul {c : ℤ} {D : Module.End K (Lambda K)} (hD : ShiftsDegree c D)
    (F : LambdaHat K) (b : ℕ → Lambda K) {e m : ℕ} (hm : (m : ℤ) + c = (e : ℤ)) :
    ∑ d ∈ range (e + 1), extVal c D F d * b (e - d)
      = ∑ d ∈ range (m + 1), D (F d : Lambda K) * b (m - d) := by
  rcases le_or_gt 0 c with hc | hc
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, c = (N : ℤ) := ⟨c.toNat, (Int.toNat_of_nonneg hc).symm⟩
    rw [show e + 1 = N + (m + 1) from by omega,
      Finset.sum_range_add (fun d => extVal (N : ℤ) D F d * b (e - d)) N (m + 1),
      Finset.sum_eq_zero (s := range N) (f := fun d => extVal (N : ℤ) D F d * b (e - d))
        (fun d hd => by
          rw [Finset.mem_range] at hd
          rw [extVal_of_lt _ _ _ (by omega), zero_mul]), zero_add]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [extVal_of_add_eq (N : ℤ) D F (n := i) (by omega),
      show e - (N + i) = m - i from by omega]
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, c = -(N : ℤ) := ⟨(-c).toNat, by omega⟩
    rw [show m + 1 = N + (e + 1) from by omega,
      Finset.sum_range_add (fun d => D (F d : Lambda K) * b (m - d)) N (e + 1),
      Finset.sum_eq_zero (s := range N) (f := fun d => D (F d : Lambda K) * b (m - d))
        (fun d hd => by
          rw [Finset.mem_range] at hd
          have hz := hD d _ (F d).2
          rw [eq_zero_of_mem_lambdaCompInt (show (d : ℤ) + -(N : ℤ) < 0 from by omega) hz,
            zero_mul]), zero_add]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [extVal_of_add_eq (-(N : ℤ)) D F (n := N + i) (by push_cast; omega),
      show m - (N + i) = e - i from by omega]

/-- **`D̂_n` past a factor of `Exp[-X/M]` in the completion**,
`D̂_n(τ^*τ f) = Exp[-X/M]·([z^n]F - [z^{n+1}]F)` with the `τ^*τ f` left general:

    D̂_n(F · Exp[-X/M]) = (D̂_n F - D̂_{n+1} F) · Exp[-X/M].

Degree by degree this is `HJO.Sym.dopInt_mul_expNegDivM` applied to each term of the convolution,
with `HJO.Sym.sum_extVal_mul` matching the two index ranges. The top term of the convolution is the
one whose factor is `h_0[-X/M] = 1`, and it is exactly the term the second sum does not have. -/
theorem completionExtension_dopInt_mul_expNegDivM (q u : K)
    (hM : ∀ k : ℕ, 1 ≤ k → (1 - q ^ k) * (1 - u ^ k) ≠ 0) (n : ℤ) (F : LambdaHat K) :
    completionExtension (dopInt_shiftsDegree q u n) (F * expNegDivM q u)
      = (completionExtension (dopInt_shiftsDegree q u n) F
          - completionExtension (dopInt_shiftsDegree q u (n + 1)) F) * expNegDivM q u := by
  refine LambdaHat.ext fun e => ?_
  have hexp : ∀ k : ℕ, (expNegDivM q u k : Lambda K)
      = plethNegDivM q u (completeHomog K k) := fun k => rfl
  have hB0 : (expNegDivM q u 0 : Lambda K) = 1 := coe_expNegDivM_zero q u
  rw [coe_completionExtension_apply, LambdaHat.coe_mul]
  have hsub : ∀ d : ℕ, (((completionExtension (dopInt_shiftsDegree q u n) F
        - completionExtension (dopInt_shiftsDegree q u (n + 1)) F) d : Lambda K))
      = extVal n (DopInt q u n) F d - extVal (n + 1) (DopInt q u (n + 1)) F d := fun d => rfl
  simp only [hsub, sub_mul, Finset.sum_sub_distrib]
  by_cases hn : n ≤ (e : ℤ)
  · obtain ⟨m, hme⟩ : ∃ m : ℕ, (m : ℤ) + n = (e : ℤ) := ⟨((e : ℤ) - n).toNat, by omega⟩
    rw [extVal_of_add_eq n (DopInt q u n) (F * expNegDivM q u) hme,
      sum_extVal_mul (dopInt_shiftsDegree q u n) F
        (fun k => (expNegDivM q u k : Lambda K)) hme]
    match m with
    | 0 =>
      rw [LambdaHat.coe_mul, Finset.sum_range_one, Finset.sum_range_one, Nat.sub_self, hexp,
        CopPower.completeHomog_zero, map_one, mul_one, mul_one,
        Finset.sum_eq_zero (s := range (e + 1))
          (f := fun d => extVal (n + 1) (DopInt q u (n + 1)) F d
            * (expNegDivM q u (e - d) : Lambda K))
          (fun d hd => by
            rw [Finset.mem_range] at hd
            rw [extVal_of_lt (n + 1) _ F (by omega), zero_mul]), sub_zero]
    | m + 1 =>
      have hm1 : (m : ℤ) + (n + 1) = (e : ℤ) := by omega
      have hkey : ∀ d ∈ range (m + 1),
          DopInt q u n ((F d : Lambda K) * (expNegDivM q u (m + 1 - d) : Lambda K))
            = DopInt q u n (F d : Lambda K) * (expNegDivM q u (m + 1 - d) : Lambda K)
              - DopInt q u (n + 1) (F d : Lambda K) * (expNegDivM q u (m - d) : Lambda K) := by
        intro d hd
        rw [Finset.mem_range] at hd
        simp only [hexp]
        rw [show m + 1 - d = (m - d) + 1 from by omega,
          dopInt_mul_expNegDivM q u hM n (m - d) (F d : Lambda K)]
        ring
      have hLHS : DopInt q u n ((F * expNegDivM q u) (m + 1) : Lambda K)
          = (∑ d ∈ range (m + 1),
              DopInt q u n (F d : Lambda K) * (expNegDivM q u (m + 1 - d) : Lambda K))
            - (∑ d ∈ range (m + 1),
              DopInt q u (n + 1) (F d : Lambda K) * (expNegDivM q u (m - d) : Lambda K))
            + DopInt q u n (F (m + 1) : Lambda K) := by
        rw [LambdaHat.coe_mul, map_sum, Finset.sum_range_succ, Finset.sum_congr rfl hkey,
          Finset.sum_sub_distrib]
        congr 1
        rw [show m + 1 - (m + 1) = 0 from by omega, hB0, mul_one]
      rw [hLHS, sum_extVal_mul (dopInt_shiftsDegree q u (n + 1)) F
          (fun k => (expNegDivM q u k : Lambda K)) hm1,
        Finset.sum_range_succ (fun d => DopInt q u n (F d : Lambda K)
          * (expNegDivM q u (m + 1 - d) : Lambda K)) (m + 1),
        show m + 1 - (m + 1) = 0 from by omega, hB0, mul_one]
      ring
  · rw [extVal_of_lt n _ _ (by omega),
      Finset.sum_eq_zero (s := range (e + 1))
        (f := fun d => extVal n (DopInt q u n) F d * (expNegDivM q u (e - d) : Lambda K))
        (fun d hd => by
          rw [Finset.mem_range] at hd
          rw [extVal_of_lt n _ F (by omega), zero_mul]),
      Finset.sum_eq_zero (s := range (e + 1))
        (f := fun d => extVal (n + 1) (DopInt q u (n + 1)) F d
          * (expNegDivM q u (e - d) : Lambda K))
        (fun d hd => by
          rw [Finset.mem_range] at hd
          rw [extVal_of_lt (n + 1) _ F (by omega), zero_mul]), sub_zero]


/-- **The conjugate shift intertwines `D_n - D_{n+1}` with `D̂_n`**, the completion half of the
calculation read on the image of `Λ`: `τ^*(D_n g - D_{n+1} g) = D̂_n(τ^* g)`.

`HJO.Sym.toLambdaHat_apply` turns `D̂_n` of the components of `g` back into the components of
`D_n g`, so this is `HJO.Sym.completionExtension_dopInt_mul_expNegDivM` at
`F = (g_d)_{d ≥ 0}`. -/
theorem nsShiftStar_dopInt_sub (q u : K)
    (hM : ∀ k : ℕ, 1 ≤ k → (1 - q ^ k) * (1 - u ^ k) ≠ 0) (n : ℤ) (g : Lambda K) :
    nsShiftStar q u (DopInt q u n g - DopInt q u (n + 1) g)
      = completionExtension (dopInt_shiftsDegree q u n) (nsShiftStar q u g) := by
  have h1 := completionExtension_dopInt_mul_expNegDivM q u hM n (toLambdaHat K g)
  rw [← toLambdaHat_apply (dopInt_shiftsDegree q u n) g,
    ← toLambdaHat_apply (dopInt_shiftsDegree q u (n + 1)) g] at h1
  have hns : ∀ h : Lambda K, nsShiftStar q u h = toLambdaHat K h * expNegDivM q u :=
    fun _ => rfl
  rw [hns, hns, map_sub]
  exact h1.symm

/-- **Mellit, the shift of a basic operator**, `HJO.Sym.nsShiftComp_comp_dopInt`:
`τ^*τ(-D_{n+1}) = D̂_n τ^*τ` as maps from `Λ` to `Λ̂`, for every `n ∈ ℤ`.

The two halves meet here. Conjugating by `τ` (`HJO.Sym.unitShift_dopInt`) turns
`τ(D_{n+1}f)` into `D_{n+1}(τf) - D_n(τf)`, so the left side is
`τ^*(D_n(τf) - D_{n+1}(τf))`, which is `D̂_n(τ^*(τf))` by
`HJO.Sym.nsShiftStar_dopInt_sub`. The two displays are those two steps, and the sign it
tracks is the one that turns the difference round.

`hM` is the nondegeneracy `HJO.Sym.eq_plethNegDivM` asks of the parameters, which the `𝕜`
discharges: it is read once, in `HJO.Sym.dopInt_mul_expNegDivM`, where the displaced `Exp[-X/M]`
splits. -/
@[hjo "lem_mellit_ns_shift_dop"]
theorem nsShiftComp_comp_dopInt (q u : K)
    (hM : ∀ k : ℕ, 1 ≤ k → (1 - q ^ k) * (1 - u ^ k) ≠ 0) (n : ℤ) :
    (nsShiftComp q u).comp (-(DopInt q u (n + 1)))
      = (completionExtension (dopInt_shiftsDegree q u n)).comp (nsShiftComp q u) := by
  refine LinearMap.ext fun f => ?_
  have hconj : unitShift (DopInt q u (n + 1) f)
      = DopInt q u (n + 1) (unitShift f) - DopInt q u n (unitShift f) := by
    rw [unitShift_dopInt q u (n + 1) f, show n + 1 - 1 = n from by ring]
  have hL : (nsShiftComp q u).comp (-(DopInt q u (n + 1))) f
      = nsShiftStar q u (DopInt q u n (unitShift f) - DopInt q u (n + 1) (unitShift f)) := by
    change nsShiftStar q u (unitShift (-(DopInt q u (n + 1) f))) = _
    rw [map_neg, hconj, neg_sub]
  rw [hL, nsShiftStar_dopInt_sub q u hM n (unitShift f)]
  rfl

end Field

end HJO.Sym

end
