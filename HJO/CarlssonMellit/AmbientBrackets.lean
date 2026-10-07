/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.Completion
public import HJO.Shuffle.MellitCompletionFrac
public import HJO.Shuffle.MellitDplusVacuum
public meta import HJO.Attr

/-! # The ambient ring `V̂°_k` of Mellit's Section 3.7, and the brackets it multiplies by

Mellit's Section 3.7 conjugates the sweep operators by multiplication by `Exp[-X/M]`, and states
the conjugated operators on the ring `V̂°_k`: the localization at `y_1y_2⋯y_k` of the completion of
`V_k = Λ ⊗_𝕜 𝕜[y_1, …, y_k]` for the grading in which `p_r` has degree `r` and each `y_i` has
degree `1`. This file is that ring.

The grading itself is `HJO.Sweep.TotalComp`, and the completion of the whole total space
`Λ[y_1, y_2, …]` for it is `HJO.Sweep.TotalHat`. Inside that commutative ring the completion of
`V_k` is a subring, namely the families all of whose members lie in `V_k` being spanned by
monomials, it is a graded subalgebra, so its graded pieces are its intersections with the pieces of
the total space and no separate grading is needed. The element `y_1y_2⋯y_k` is homogeneous of
degree `k` and lies in that subring, and `V̂°_k` is the localization there.

The localization is faithful, because the completion is a domain — the leading term of a
convolution of two nonzero families is the product of their leading terms — and `y_1y_2⋯y_k` is
therefore a non-zerodivisor. For the same reason `V̂°_k` is a subring of the fraction field
`HJO.Sweep.HatFrac` of the completion, which is where `d^*_+` and `τ^*_k` are already defined, so
the two readings of Section 3.7's operators agree on the ring the section states them on.

The two plethystic brackets the section multiplies by are `σ_{-1/M} : f ↦ f[-X/M]`, the `𝕜`-algebra
endomorphism of `Λ` sending `p_k` to `-p_k/((1-q^k)(1-u^k))`, and the element
`Exp[-X/M] = ∑_{d ≥ 0} h_d[-X/M]` of the completion `Λ̂` of `Λ`. Both are
`HJO/Shuffle/Completion.lean`'s `HJO.Sym.plethNegDivM` and `HJO.Sym.expNegDivM`; what is added
here is the characterisation of each — the property that identifies it among all candidates, so
that a reader recognises the bracket without unfolding it.

## Main definitions

* `HJO.Sweep.pieceHat` — the completion of `V_k` for the grading above, as a subring of the
  completion of the total space.
* `HJO.Sweep.auxVarProdHat` — `y_1y_2⋯y_k` read in that completion, homogeneous of degree `k`.
* `HJO.Sweep.NsAmbient` — the ring `V̂°_k`, the localization of the completion of `V_k` at
  `y_1y_2⋯y_k`.

## Main results

* `HJO.Sym.eq_plethNegDivM` and `HJO.Sym.eq_expNegDivM_iff` — the two brackets are determined by
  the formulae that define them: an algebra endomorphism of `Λ` sending each `p_k` to
  `-p_k/((1-q^k)(1-u^k))` is `σ_{-1/M}`, and a family whose member in degree `d` is `h_d[-X/M]` is
  `Exp[-X/M]`.
* `HJO.Sweep.algebraMap_nsAmbient_injective` — the localization is faithful: the completion of
  `V_k` embeds in `V̂°_k`.
* `HJO.Sweep.nsAmbientToHatFrac_injective` — `V̂°_k` embeds in the fraction field of the completion
  of the total space, on which the section's conjugated operators are already defined.

## Implementation notes

As usually defined, `V̂°_k` is built from `V_k` alone; here it is built inside the one total space
`HJO.Sweep.Total` in which every `V_k` is realised, following the convention of
`HJO/Shuffle/SweepModule.lean`. The two agree: `HJO.Sweep.pieceHat` is by definition the
families supported in `V_k`, and the graded pieces of `V_k` are the intersections of `V_k` with
those of the total space.

The nonvanishing `(1-q^k)(1-u^k) ≠ 0`, which the formula for `σ_{-1/M}` needs and which holds
whenever `q` and `u` satisfy no polynomial relation over `𝕜`, is not a hypothesis
of `HJO.Sym.plethNegDivM`: the inverse there is the field inverse, which is total. It is not a
hypothesis of the characterisation below either, that statement comparing two substitutions with
the same scalars whatever those scalars are.

## References

Following A. Mellit, *Toric braids and
`(m,n)`-parking functions*, §3.7.
-/

@[expose] public section

open Finset

attribute [hjo "def_pleth_negdivm"] HJO.Sym.plethNegDivM HJO.Sym.plethNegDivM_powerSum
attribute [hjo "def_pleth_exp_negdivm"] HJO.Sym.expNegDivM HJO.Sym.coe_expNegDivM

namespace HJO.Sym

variable {K : Type*} [Field K] [Algebra ℚ K]

omit [Algebra ℚ K] in
/-- **`σ_{-1/M}` is determined by its values on the power sums.** A `𝕜`-algebra endomorphism of `Λ`
sending `p_k` to `-p_k/((1-q^k)(1-u^k))` for every `k ≥ 1` is `HJO.Sym.plethNegDivM`, the power sums
freely generating `Λ`.

This is the form in which the bracket `f ↦ f[-X/M]` is recognised: a substitution arising from some
other construction is this one as soon as its scalars match, with no unfolding. -/
@[hjo "def_pleth_negdivm"]
theorem eq_plethNegDivM (q u : K) {φ : Lambda K →ₐ[K] Lambda K}
    (hφ : ∀ k : ℕ, 1 ≤ k → φ (powerSum K k)
      = MvPolynomial.C (-((1 - q ^ k) * (1 - u ^ k))⁻¹) * powerSum K k) :
    φ = plethNegDivM q u := by
  refine MvPolynomial.algHom_ext fun i => ?_
  have hx : (MvPolynomial.X i : Lambda K) = powerSum K (i + 1) := by
    rw [powerSum, Nat.add_sub_cancel]
  rw [hx, hφ (i + 1) (by omega), plethNegDivM_powerSum q u (by omega)]

/-- **`Exp[-X/M]` is determined by its members.** An element of the completion `Λ̂` is
`HJO.Sym.expNegDivM` exactly when its member in degree `d` is `h_d[-X/M]` for every `d`, which is
the formula defining it; the degree condition is carried by the type, so no homogeneity clause
appears. -/
@[hjo "def_pleth_exp_negdivm"]
theorem eq_expNegDivM_iff (q u : K) {F : LambdaHat K} :
    F = expNegDivM q u ↔ ∀ d, (F d : Lambda K) = plethNegDivM q u (completeHomog K d) :=
  ⟨fun h d => by rw [h, coe_expNegDivM], fun h => LambdaHat.ext fun d => by
    rw [h d, coe_expNegDivM]⟩

end HJO.Sym

namespace HJO.Sweep

/-! ### The completion of `V_k` -/

section CommRingBase

variable {L : Type*} [CommRing L]

/-- **The completion of `V_k`** for the grading in which `p_r` has degree `r` and each `y_i` has
degree `1`, as a subring of `HJO.Sweep.TotalHat`: the families every one of whose members lies in
`V_k`.

`V_k` is spanned by monomials, hence a graded subalgebra of the total space, so its graded piece of
degree `d` is its intersection with `HJO.Sweep.TotalComp L d` and this is the completion of `V_k`
for the induced grading rather than merely the families of the total space that happen to be
supported in `V_k`. -/
@[hjo "def_mellit_ns_ambient"]
noncomputable def pieceHat (L : Type*) [CommRing L] (k : ℕ) : Subring (TotalHat L) where
  carrier := {F | ∀ d, (F d : Total L) ∈ piece L k}
  mul_mem' {F G} hF hG d := by
    rw [TotalHat.coe_mul]
    exact sum_mem fun e _ => mul_mem (hF e) (hG (d - e))
  one_mem' d := by
    rw [TotalHat.coe_one]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  add_mem' {F G} hF hG d := by
    rw [TotalHat.coe_add]
    exact add_mem (hF d) (hG d)
  zero_mem' d := by
    rw [TotalHat.coe_zero]
    exact zero_mem _
  neg_mem' {F} hF d := neg_mem (hF d)

theorem mem_pieceHat {k : ℕ} {F : TotalHat L} :
    F ∈ pieceHat L k ↔ ∀ d, (F d : Total L) ∈ piece L k := Iff.rfl

/-- The completions of the `V_k` increase with `k`, as the `V_k` do. -/
theorem pieceHat_mono {k l : ℕ} (h : k ≤ l) : pieceHat L k ≤ pieceHat L l :=
  fun _ hF d => piece_mono h (hF d)

end CommRingBase

/-! ### The element `y_1y_2⋯y_k` -/

section Field

variable {L : Type*} [Field L]

/-- **`y_1y_2⋯y_k` is homogeneous of degree `k`**, each of its `k` letters having degree `1`. -/
theorem auxVarProd_mem_totalComp (L : Type*) [Field L] (k : ℕ) :
    auxVarProd L k ∈ TotalComp L k := by
  induction k with
  | zero => rw [auxVarProd_zero]; exact one_mem_totalComp L
  | succ n ih => rw [auxVarProd_succ]; exact mul_mem_totalComp ih (auxVar_mem_totalComp L (n + 1))

/-- **`y_1y_2⋯y_k` lies in `V_k`**, all of its letters being among `y_1, …, y_k`. -/
theorem auxVarProd_mem_piece (L : Type*) [Field L] (k : ℕ) : auxVarProd L k ∈ piece L k := by
  rw [auxVarProd]
  refine prod_mem fun j hj => ?_
  have h := auxVar_mem_piece (L := L) (i := j + 1) (k := k) (by omega)
    (by rw [Finset.mem_range] at hj; omega)
  rwa [auxVar, Nat.add_sub_cancel] at h

/-- **`y_1y_2⋯y_k` is nonzero**, being a product of distinct variables of a polynomial ring over a
domain. -/
theorem auxVarProd_ne_zero (L : Type*) [Field L] (k : ℕ) : auxVarProd L k ≠ 0 := by
  rw [auxVarProd]
  exact Finset.prod_ne_zero_iff.2 fun j _ => MvPolynomial.X_ne_zero j

/-- **`y_1y_2⋯y_k` read in the completion of `V_k`**: the family concentrated in degree `k`, where
its value is `y_1y_2⋯y_k`. This is the element `V̂°_k` inverts. -/
noncomputable def auxVarProdHat (L : Type*) [Field L] (k : ℕ) : pieceHat L k :=
  ⟨TotalHat.ofComp (auxVarProd L k) (auxVarProd_mem_totalComp L k), fun d => by
    rw [TotalHat.coe_ofComp]
    split_ifs
    · exact auxVarProd_mem_piece L k
    · exact zero_mem _⟩

theorem coe_auxVarProdHat (L : Type*) [Field L] (k d : ℕ) :
    (((auxVarProdHat L k : pieceHat L k) : TotalHat L) d : Total L)
      = if d = k then auxVarProd L k else 0 :=
  TotalHat.coe_ofComp (auxVarProd L k) (auxVarProd_mem_totalComp L k) d

theorem coe_auxVarProdHat_self (L : Type*) [Field L] (k : ℕ) :
    (((auxVarProdHat L k : pieceHat L k) : TotalHat L) k : Total L) = auxVarProd L k := by
  rw [coe_auxVarProdHat]
  simp

theorem auxVarProdHat_ne_zero (L : Type*) [Field L] (k : ℕ) : auxVarProdHat L k ≠ 0 := by
  intro h
  have h0 : (((auxVarProdHat L k : pieceHat L k) : TotalHat L) k : Total L) = 0 := by
    rw [h]; rfl
  rw [coe_auxVarProdHat_self] at h0
  exact auxVarProd_ne_zero L k h0

/-! ### The ambient ring -/

/-- **The ambient ring `V̂°_k` of Mellit's Section 3.7**: the localization at `y_1y_2⋯y_k` of the
completion of `V_k` for the grading in which `p_r` has degree `r` and each `y_i` has degree `1`.

The localization is faithful — `HJO.Sweep.algebraMap_nsAmbient_injective` — the completion being a
domain and `y_1y_2⋯y_k` therefore a non-zerodivisor in it, and
`HJO.Sweep.nsAmbientToHatFrac_injective` embeds `V̂°_k` in the fraction field of the completion of
the total space, which is the ambient on which the section's conjugated operators are defined. -/
@[hjo "def_mellit_ns_ambient"]
abbrev NsAmbient (L : Type*) [Field L] (k : ℕ) : Type _ :=
  Localization.Away (auxVarProdHat L k)

/-- Every power of `y_1y_2⋯y_k` is a non-zerodivisor of the completion of `V_k`, that ring being a
subring of a domain. -/
theorem powers_auxVarProdHat_le_nonZeroDivisors (L : Type*) [Field L] (k : ℕ) :
    Submonoid.powers (auxVarProdHat L k) ≤ nonZeroDivisors (pieceHat L k) :=
  powers_le_nonZeroDivisors_of_noZeroDivisors (auxVarProdHat_ne_zero L k)

/-- **The localization is faithful**: the completion of `V_k` embeds in `V̂°_k`. This is the
basic remark on the ambient, and it is what lets a statement about `V̂°_k` be read back on
the completion. -/
theorem algebraMap_nsAmbient_injective (L : Type*) [Field L] (k : ℕ) :
    Function.Injective (algebraMap (pieceHat L k) (NsAmbient L k)) :=
  IsLocalization.injective _ (powers_auxVarProdHat_le_nonZeroDivisors L k)

theorem injective_toHatFrac_comp_subtype (L : Type*) [Field L] (k : ℕ) :
    Function.Injective ((algebraMap (TotalHat L) (HatFrac L)).comp (pieceHat L k).subtype) :=
  (IsFractionRing.injective (TotalHat L) (HatFrac L)).comp Subtype.val_injective

theorem isUnit_toHatFrac_of_mem_powers (L : Type*) [Field L] (k : ℕ)
    (s : Submonoid.powers (auxVarProdHat L k)) :
    IsUnit (((algebraMap (TotalHat L) (HatFrac L)).comp (pieceHat L k).subtype) s) := by
  rw [isUnit_iff_ne_zero]
  intro h
  exact nonZeroDivisors.coe_ne_zero
    ⟨(s : pieceHat L k), powers_auxVarProdHat_le_nonZeroDivisors L k s.2⟩
    (injective_toHatFrac_comp_subtype L k (by rw [h, map_zero]))

/-- **`V̂°_k` inside the fraction field of the completion of the total space.** The section's
conjugated operators `d^*_+` and `τ^*_k` are defined on that field, and this is the map along which
they restrict to the ring the section states them on. -/
noncomputable def nsAmbientToHatFrac (L : Type*) [Field L] (k : ℕ) :
    NsAmbient L k →+* HatFrac L :=
  IsLocalization.lift (isUnit_toHatFrac_of_mem_powers L k)

/-- **`V̂°_k` is a subring of the fraction field of the completion.** Both the completion of `V_k`
and the inverted element are read faithfully there: the first by
`HJO.Sweep.injective_toHatFrac_comp_subtype` and the second because a nonzero element of a domain
becomes a unit in its fraction field. -/
theorem nsAmbientToHatFrac_injective (L : Type*) [Field L] (k : ℕ) :
    Function.Injective (nsAmbientToHatFrac L k) :=
  (IsLocalization.lift_injective_iff _).2 fun _ _ =>
    ⟨fun h => congrArg _ (algebraMap_nsAmbient_injective L k h),
      fun h => congrArg _ (injective_toHatFrac_comp_subtype L k h)⟩

end Field

end HJO.Sweep
