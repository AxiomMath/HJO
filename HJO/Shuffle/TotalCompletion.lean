/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.TotalGrading
public import HJO.Shuffle.QShiftInverse
public meta import HJO.Attr

/-! # The completion of the sweep's total space, and the corner multiplier `E_k`

The completion of `HJO.Sweep.Total` for the grading of `HJO/Shuffle/TotalGrading.lean`, and
the element of it that Mellit's Section 3.7 multiplies by: the corner multiplier
`E_k = Exp[-X/M - (y_1 + ⋯ + y_k)/(u-1)]` of `HJO.Sweep.cornerMultiplier`.

## `Exp[A] = ∑_n h_n[A]`, and what that buys

Mellit writes `E_k` as `exp` of a series in the `p_r` and the `y_i`, with the plethystic exponential
`Exp[A] = exp(∑_{r≥1} p_r[A]/r)`. The convention already in force twice in this library — at
`HJO.Sym.DopInt`, whose `∑_r(-z)^re_r` is `∑_r h_r[-zX]`, and at `HJO.Sweep.dminus`, which names
`∑_n(-1)^ne_ny_k^{-n}` as `Exp[-y_k^{-1}X]` — reads the same series as `Exp[A] = ∑_{n ≥ 0} h_n[A]`,
and `HJO.Sym.expNegDivM` already builds `Exp[-X/M]` that way.

That reading is what makes the multiplier elementary here. The member of `E_k` in degree `n` is
`h_n[A_k]`, the image of the complete homogeneous function `h_n` under the *substitution*
`HJO.Sweep.cornerAlphabet` realising the alphabet `A_k = -X/M - (y_1+⋯+y_k)/(u-1)`; it is
automatically homogeneous of degree `n`, because `h_n` is and the substitution sends `p_r` to an
element of degree `r`. No exponential series, no factorials, and — since the two lemmas below
compare two *substitutions* on the generators — no ring axiom of the completion is read.

## Main definitions

* `HJO.Sweep.TotalHat` — the completion: families `(F_d)_{d ≥ 0}` with `F_d` homogeneous of degree
  `d`, with componentwise addition and `𝕜`-action and the convolution product.
* `HJO.Sweep.hatMap` — the componentwise extension of a degree-preserving algebra endomorphism of
  the total space, which is how `HJO.Sweep.hatFracDplusStar` reads `τ_{k,i}` and `cy_{k+1}` on the
  completion.
* `HJO.Sweep.cornerAlphabet`, `HJO.Sweep.cornerMultiplier` — the alphabet `A_k` as a substitution,
  and `E_k` of `HJO.Sweep.cornerMultiplier`.

## Main results

* `HJO.Sweep.hatMap_qshift_cornerMultiplier`,
  `τ_{k+1,k+1}(E_k) = E_{k+1}`.
* `HJO.Sweep.hatMap_qshiftNeg_cornerMultiplier`, `τ^-_{k,k}(E_k) = E_{k-1}`, off the previous one
  and `HJO.Sweep.qshiftNeg_qshift`.
* `HJO.Sweep.coe_cornerMultiplier_zero` — at `k = 0` the multiplier is the `Exp[-X/M]` of
  `HJO.Sym.expNegDivM`, read in the total space. So the two readings of Section 3.7's multiplier
  are one object and `HJO.Sweep.cornerMultiplier` does not fork from
  `HJO.Sym.nsShiftStar`.

## Where `q^r ≠ 1` enters, and why it is not on the definition

`HJO.Sweep.hatMap_qshift_cornerMultiplier` is where `(q^r-1)` cancels: `τ_{k+1,k+1}` adds
`(q^r-1)y_{k+1}^r` to `p_r`, and divided by `p_r[M] = (q^r-1)(u^r-1)` that is `y_{k+1}^r/(u^r-1)`,
the term `E_{k+1}` has and `E_k` does not. The cancellation needs `q^r ≠ 1`, and the lemma is false
from `r = 2` on under the monomial reading of the added letter.
The hypothesis sits on the two lemmas and not on `cornerAlphabet`, following
`HJO.Sym.plethNegDivM`: the definition uses the field inverse, which is total, and no statement
reads its value at a degenerate parameter.

## What this file is *not*

`HJO.Sweep.pieceHat` asks for the **localization at `y_1⋯y_k`** of this completion. That
localization is not built here, and no result of Section 3.7 reads both halves at once: the
multiplier, `τ^*_k` and `d^*_+` live in the completion, while `τ_k` of `HJO.Sweep.nsShiftExt`
divides by the `y_i` and lives in the localization of the *polynomial* ring. The common ambient is
read only when the two are composed, inside the proof of `HJO.Sym.nsShiftComp_comp_smul_map`.

## References

A. Mellit, *Toric braids and `(m,n)`-parking functions*, §3.7, for `HJO.Sweep.pieceHat`,
`HJO.Sweep.cornerMultiplier`, `HJO.Sweep.hatMap_qshift_cornerMultiplier` and
`HJO.Sweep.hatMap_qshiftNeg_cornerMultiplier`.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Sweep

/-! ### The completion -/

/-- **The completion of the total space by degree**: the families `(F_d)_{d ≥ 0}` with `F_d`
homogeneous of degree `d`, read as a dependent function into the graded pieces so that the degree
condition is carried by the type rather than by a side hypothesis. This is the completion half of
`HJO.Sweep.pieceHat`, and it is `HJO.Sym.LambdaHat` with the auxiliary variables admitted.

Componentwise addition and the `𝕜`-action are the ones a product of submodules already has; the
product is the convolution of `HJO.Sweep.TotalHat.coe_mul`. -/
abbrev TotalHat (L : Type*) [CommRing L] : Type _ := ∀ d : ℕ, TotalComp L d

namespace TotalHat

variable {L : Type*} [CommRing L]

/-- Two families agree when their members do. -/
@[ext]
theorem ext {F G : TotalHat L} (h : ∀ d, (F d : Total L) = (G d : Total L)) : F = G :=
  funext fun d => Subtype.ext (h d)

theorem coe_add (F G : TotalHat L) (d : ℕ) :
    ((F + G) d : Total L) = (F d : Total L) + (G d : Total L) := rfl

theorem coe_sub (F G : TotalHat L) (d : ℕ) :
    ((F - G) d : Total L) = (F d : Total L) - (G d : Total L) := rfl

theorem coe_smul (r : L) (F : TotalHat L) (d : ℕ) :
    ((r • F) d : Total L) = r • (F d : Total L) := rfl

theorem coe_zero (d : ℕ) : ((0 : TotalHat L) d : Total L) = 0 := rfl

/-- **The convolution product**: `(FG)_d = ∑_{e = 0}^{d} F_e G_{d-e}`, a sum over `{0, …, d}` each
of whose terms is homogeneous of degree `d` because `e + (d - e) = d`. -/
noncomputable instance : Mul (TotalHat L) where
  mul F G := fun d => ⟨∑ e ∈ range (d + 1), (F e : Total L) * (G (d - e) : Total L),
    Submodule.sum_mem _ fun e he => by
      have h := mul_mem_totalComp (F e).2 (G (d - e)).2
      rw [Finset.mem_range] at he
      rwa [show e + (d - e) = d from by omega] at h⟩

theorem coe_mul (F G : TotalHat L) (d : ℕ) :
    ((F * G) d : Total L) = ∑ e ∈ range (d + 1), (F e : Total L) * (G (d - e) : Total L) := rfl

/-- The unit of the convolution: `1` in degree `0` and `0` above it. -/
noncomputable instance : One (TotalHat L) where
  one := fun d => ⟨if d = 0 then 1 else 0, by
    split_ifs with h
    · subst h; exact one_mem_totalComp L
    · exact zero_mem _⟩

theorem coe_one (d : ℕ) : ((1 : TotalHat L) d : Total L) = if d = 0 then 1 else 0 := rfl

end TotalHat

/-! ### Reading a degree-preserving substitution on the completion -/

section Ext

variable {L : Type*} [CommRing L]

/-- A `𝕜`-algebra endomorphism of the total space preserving every graded piece. This is the
hypothesis `HJO.Sweep.hatFracDplusStar` states as "homogeneous of degree `0`", and it is what makes
the extension to the completion exist and be unique: a continuous map is determined by its members,
and a degree-preserving one acts on each member separately. -/
def PreservesTotalComp (D : Total L →ₐ[L] Total L) : Prop :=
  ∀ d : ℕ, ∀ F ∈ TotalComp L d, D F ∈ TotalComp L d

/-- **The extension of a degree-preserving substitution to the completion**, applied to each member
separately. -/
noncomputable def hatMap {D : Total L →ₐ[L] Total L} (hD : PreservesTotalComp D)
    (F : TotalHat L) : TotalHat L := fun d => ⟨D (F d), hD d _ (F d).2⟩

theorem coe_hatMap {D : Total L →ₐ[L] Total L} (hD : PreservesTotalComp D) (F : TotalHat L)
    (d : ℕ) : (hatMap hD F d : Total L) = D (F d) := rfl

/-- **The extension is multiplicative for the convolution.** This is what
`HJO.Sweep.hatFracDplusStar_nsShiftStarFrac` reads when it takes `d^*_+` past a product. -/
theorem hatMap_mul {D : Total L →ₐ[L] Total L} (hD : PreservesTotalComp D) (F G : TotalHat L) :
    hatMap hD (F * G) = hatMap hD F * hatMap hD G :=
  TotalHat.ext fun d => by
    rw [coe_hatMap, TotalHat.coe_mul, TotalHat.coe_mul, map_sum]
    exact Finset.sum_congr rfl fun e _ => by rw [map_mul, coe_hatMap, coe_hatMap]

theorem hatMap_one {D : Total L →ₐ[L] Total L} (hD : PreservesTotalComp D) :
    hatMap hD (1 : TotalHat L) = 1 :=
  TotalHat.ext fun d => by
    rw [coe_hatMap, TotalHat.coe_one]
    split_ifs
    · exact map_one D
    · exact map_zero D

theorem hatMap_add {D : Total L →ₐ[L] Total L} (hD : PreservesTotalComp D) (F G : TotalHat L) :
    hatMap hD (F + G) = hatMap hD F + hatMap hD G :=
  TotalHat.ext fun d => by
    rw [coe_hatMap, TotalHat.coe_add, TotalHat.coe_add, coe_hatMap, coe_hatMap, map_add]

end Ext

section Field

variable {L : Type*} [Field L]

theorem preservesTotalComp_qshift (q : L) (i : ℕ) : PreservesTotalComp (qshift q i) :=
  fun _ _ hF => qshift_mem_totalComp q i hF

theorem preservesTotalComp_qshiftNeg (q : L) (i : ℕ) : PreservesTotalComp (qshiftNeg q i) :=
  fun _ _ hF => qshiftNeg_mem_totalComp q i hF

theorem preservesTotalComp_cycleShift (u : L) (k : ℕ) :
    PreservesTotalComp ((cycleShift u k).restrictScalars L) :=
  fun _ _ hF => cycleShift_mem_totalComp u k hF

end Field

/-! ### The corner multiplier -/

section Multiplier

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The alphabet `A_k = -X/M - (y_1 + ⋯ + y_k)/(u-1)`**, as the substitution it is: the
`𝕜`-algebra homomorphism from `Λ` to the total space with
`p_r ↦ -(p_r/((q^r-1)(u^r-1)) + (y_1^r + ⋯ + y_k^r)/(u^r-1))`.

The two scalars are those of the definition: `p_r[M] = (q^r-1)(u^r-1)` is the coefficient
`HJO.Sym.plethShift` fixes, and the alphabet `y_i/(u-1)` has `p_r = y_i^r/(u^r-1)` because `p_r` is
multiplicative on products of alphabets and `p_r[u-1] = u^r-1`. -/
noncomputable def cornerAlphabet (q u : L) (k : ℕ) : Sym.Lambda L →ₐ[L] Total L :=
  MvPolynomial.aeval fun i : ℕ =>
    -(scal (((q ^ (i + 1) - 1) * (u ^ (i + 1) - 1))⁻¹) *
        MvPolynomial.C (Sym.powerSum L (i + 1))
      + scal ((u ^ (i + 1) - 1)⁻¹) * ∑ j ∈ range k, (auxVar (j + 1) : Total L) ^ (i + 1))

omit [Algebra ℚ L] in
/-- The defining formula, read against the index convention of `HJO.Sym.powerSum`. -/
theorem cornerAlphabet_powerSum (q u : L) (k i : ℕ) :
    cornerAlphabet q u k (Sym.powerSum L (i + 1))
      = -(scal (((q ^ (i + 1) - 1) * (u ^ (i + 1) - 1))⁻¹) *
        MvPolynomial.C (Sym.powerSum L (i + 1))
      + scal ((u ^ (i + 1) - 1)⁻¹) * ∑ j ∈ range k, (auxVar (j + 1) : Total L) ^ (i + 1)) := by
  have hx : (Sym.powerSum L (i + 1) : Sym.Lambda L) = MvPolynomial.X i := by
    rw [Sym.powerSum, Nat.add_sub_cancel]
  conv_lhs => rw [hx]
  rw [cornerAlphabet, MvPolynomial.aeval_X]

omit [Algebra ℚ L] in
/-- **The alphabet substitution preserves degree.** Each `p_r` goes to a combination of `p_r` and
of the `y_i^r`, all of degree `r`; the scalars cost nothing. -/
theorem cornerAlphabet_mem_totalComp (q u : L) (k : ℕ) {d : ℕ} {f : Sym.Lambda L}
    (hf : f ∈ Sym.LambdaComp L d) : cornerAlphabet q u k f ∈ TotalComp L d := by
  have h := Sym.mem_of_mem_lambdaComp (TotalCompInt L) (one_mem_totalCompInt L)
    (fun {_ _ _ _} hx hy => mul_mem_totalCompInt hx hy) (cornerAlphabet q u k) (fun i => by
      rw [show (MvPolynomial.X i : Sym.Lambda L) = Sym.powerSum L (i + 1) by
          rw [Sym.powerSum, Nat.add_sub_cancel],
        cornerAlphabet_powerSum, show ((i : ℤ) + 1) = (((i + 1 : ℕ)) : ℤ) by push_cast; ring,
        totalCompInt_natCast]
      refine neg_mem (add_mem ?_ ?_)
      · have h2 := mul_mem_totalComp (scal_mem_totalComp
          (((q ^ (i + 1) - 1) * (u ^ (i + 1) - 1))⁻¹)) (powerSum_mem_totalComp L i)
        simpa using h2
      · have hsum : (∑ j ∈ range k, (auxVar (j + 1) : Total L) ^ (i + 1))
            ∈ TotalComp L (i + 1) :=
          Submodule.sum_mem _ fun j _ => by
            have h3 := pow_mem_totalComp (auxVar_mem_totalComp L (j + 1)) (i + 1)
            simpa using h3
        have h2 := mul_mem_totalComp (scal_mem_totalComp ((u ^ (i + 1) - 1)⁻¹)) hsum
        simpa using h2) hf
  rwa [totalCompInt_natCast] at h

/-- **The corner multiplier `E_k`.** `HJO.Sweep.cornerMultiplier`:
`E_k = Exp[-X/M - (y_1+⋯+y_k)/(u-1)]`, the element of the completion whose member in degree `n` is
`h_n` of that alphabet.

Its member in degree `0` is `h_0 = 1`, so it has constant term `1`, which is the property
`HJO.Sym.nsShiftComp_injective` reads of the multiplier at `k = 0`; and
`HJO.Sweep.coe_cornerMultiplier_zero` identifies that case with
`HJO.Sym.expNegDivM`. -/
@[hjo "def_mellit_ns_multiplier"]
noncomputable def cornerMultiplier (q u : L) (k : ℕ) : TotalHat L := fun d =>
  ⟨cornerAlphabet q u k (Sym.completeHomog L d),
    cornerAlphabet_mem_totalComp q u k (Sym.completeHomog_mem_lambdaComp L d)⟩

theorem coe_cornerMultiplier (q u : L) (k d : ℕ) :
    (cornerMultiplier q u k d : Total L) = cornerAlphabet q u k (Sym.completeHomog L d) := rfl

/-! ### The two substitutions against the multiplier -/

omit [Algebra ℚ L] in
/-- **The letter substitution advances the alphabet.** `τ_{k+1,k+1}` fixes every `y_i` and adds
`(q^r-1)y_{k+1}^r` to `p_r`; divided by `p_r[M] = (q^r-1)(u^r-1)` that added term is exactly
`y_{k+1}^r/(u^r-1)`, which is the one term by which `A_{k+1}` exceeds `A_k`.

**The cancellation of `q^r-1` is where the convention of `HJO.Sweep.qshift` is load-bearing**: the
substitution adds the *virtual* alphabet `qy_{k+1} - y_{k+1}`, contributing `q^r-1`, which is the
first factor of `p_r[M]`. Under the monomial reading, contributing `(q-1)^r`, nothing cancels. -/
theorem qshift_cornerAlphabet (q u : L) (hq : ∀ r : ℕ, 1 ≤ r → q ^ r ≠ 1) (k : ℕ) :
    (qshift q (k + 1)).comp (cornerAlphabet q u k) = cornerAlphabet q u (k + 1) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  have hx : (MvPolynomial.X i : Sym.Lambda L) = Sym.powerSum L (i + 1) := by
    rw [Sym.powerSum, Nat.add_sub_cancel]
  have hkey : (scal (((q ^ (i + 1) - 1) * (u ^ (i + 1) - 1))⁻¹) : Total L) *
      scal (q ^ (i + 1) - 1) = scal ((u ^ (i + 1) - 1)⁻¹) := by
    rw [← scal_mul]
    congr 1
    field_simp [sub_ne_zero.2 (hq (i + 1) (by omega))]
  rw [AlgHom.comp_apply, hx, cornerAlphabet_powerSum, cornerAlphabet_powerSum,
    map_neg, map_add, map_mul, map_mul, map_sum, qshift_scal, qshift_scal, qshift_powerSum,
    Finset.sum_range_succ]
  have hsum : ∀ j : ℕ, qshift q (k + 1) ((auxVar (j + 1) : Total L) ^ (i + 1))
      = (auxVar (j + 1) : Total L) ^ (i + 1) := by
    intro j
    rw [map_pow, qshift_auxVar_apply]
  simp only [hsum]
  rw [mul_add, ← mul_assoc, hkey]
  ring

/-- **The letter substitution advances the corner multiplier.**
`HJO.Sweep.hatMap_qshift_cornerMultiplier`: `τ_{k+1,k+1}(E_k) = E_{k+1}`.

The usual argument is that `τ_{k+1,k+1}` is continuous and so commutes with the exponential,
leaving the exponent to be compared. Under the reading `Exp[A] = ∑_n h_n[A]` there is no
exponential to commute with: the member in degree `n` is `h_n` of the alphabet, the substitution is
degree-preserving so acts on it memberwise, and what is compared is the two alphabets — which is
`HJO.Sweep.qshift_cornerAlphabet`, an identity of substitutions checked on the generators. -/
@[hjo "lem_mellit_ns_multiplier_qshift"]
theorem hatMap_qshift_cornerMultiplier (q u : L) (hq : ∀ r : ℕ, 1 ≤ r → q ^ r ≠ 1) (k : ℕ) :
    hatMap (preservesTotalComp_qshift q (k + 1)) (cornerMultiplier q u k)
      = cornerMultiplier q u (k + 1) :=
  TotalHat.ext fun d => by
    rw [coe_hatMap, coe_cornerMultiplier, coe_cornerMultiplier, ← AlgHom.comp_apply,
      qshift_cornerAlphabet q u hq k]

/-- **The inverse letter substitution retracts the corner multiplier.**
`HJO.Sweep.hatMap_qshiftNeg_cornerMultiplier`: `τ^-_{k,k}(E_k) = E_{k-1}`, stated at `k + 1` so that
the hypothesis `k ≥ 1` needs no truncated subtraction.

Exactly the proof: `E_{k+1}` is `τ_{k+1,k+1}(E_k)` by the previous lemma, and the two
substitutions are inverse by `HJO.Sweep.qshiftNeg_qshift` — which is `HJO.Sweep.qshiftNeg_qshift`,
proved on the total space and therefore available memberwise on the completion without a separate
"the argument with `V_k` replaced by `V̂°_k`". -/
@[hjo "lem_mellit_ns_multiplier_qshift_neg"]
theorem hatMap_qshiftNeg_cornerMultiplier (q u : L) (hq : ∀ r : ℕ, 1 ≤ r → q ^ r ≠ 1) (k : ℕ) :
    hatMap (preservesTotalComp_qshiftNeg q (k + 1)) (cornerMultiplier q u (k + 1))
      = cornerMultiplier q u k :=
  TotalHat.ext fun d => by
    rw [coe_hatMap, coe_cornerMultiplier, coe_cornerMultiplier,
      ← qshift_cornerAlphabet q u hq k, AlgHom.comp_apply, qshiftNeg_qshift]

/-! ### The multiplier at `k = 0` is the `Exp[-X/M]` of `HJO.Sym.expNegDivM` -/

omit [Algebra ℚ L] in
/-- At `k = 0` the alphabet is `-X/M`, the substitution `HJO.Sym.plethNegDivM` read in the total
space. The two scalars agree on the nose: `-((1-q^r)(1-u^r))⁻¹ = -((q^r-1)(u^r-1))⁻¹`. -/
theorem cornerAlphabet_zero (q u : L) :
    cornerAlphabet q u 0
      = (IsScalarTower.toAlgHom L (Sym.Lambda L) (Total L)).comp (Sym.plethNegDivM q u) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  have hx : (MvPolynomial.X i : Sym.Lambda L) = Sym.powerSum L (i + 1) := by
    rw [Sym.powerSum, Nat.add_sub_cancel]
  rw [hx, cornerAlphabet_powerSum, AlgHom.comp_apply,
    Sym.plethNegDivM_powerSum q u (k := i + 1) (by omega)]
  rw [Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
  have hC : (IsScalarTower.toAlgHom L (Sym.Lambda L) (Total L))
      (MvPolynomial.C (-((1 - q ^ (i + 1)) * (1 - u ^ (i + 1)))⁻¹) * Sym.powerSum L (i + 1))
      = scal (-((1 - q ^ (i + 1)) * (1 - u ^ (i + 1)))⁻¹) *
        MvPolynomial.C (Sym.powerSum L (i + 1)) := by
    rw [map_mul]
    rfl
  rw [hC, show ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1)))
      = ((q ^ (i + 1) - 1) * (u ^ (i + 1) - 1)) by ring]
  rw [scal_neg]
  ring

/-- **`E_0` is `Exp[-X/M]`.** So the multiplier of `HJO.Sweep.cornerMultiplier` and the one
`HJO.Sym.nsShiftStar` multiplies by are the same element, and the two completions agree where
they overlap: `HJO.Sym.expNegDivM` read in the total space is the `k = 0` member of the family
here. -/
theorem coe_cornerMultiplier_zero (q u : L) (d : ℕ) :
    (cornerMultiplier q u 0 d : Total L)
      = MvPolynomial.C (Sym.expNegDivM q u d : Sym.Lambda L) := by
  rw [coe_cornerMultiplier, cornerAlphabet_zero, AlgHom.comp_apply, Sym.coe_expNegDivM]
  rfl

/-- **`E_k` has `1` in degree zero**, since `h_0 = 1` and the alphabet substitution is an algebra
map. This holds at every `q` and `u`, including the degenerate ones. -/
theorem coe_cornerMultiplier_zero_degree (q u : L) (k : ℕ) :
    (cornerMultiplier q u k 0 : Total L) = 1 := by
  rw [coe_cornerMultiplier, UkRegular.completeHomog_zero L, map_one]

end Multiplier

end HJO.Sweep

end
