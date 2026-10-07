/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.Grading
public import HJO.Shuffle.MellitUnitShift
public meta import HJO.Attr

/-! # The completion of `Λ` by degree, and the extension of a degree shift to it

`HJO/Shuffle/Grading.lean` defines the graded pieces `Λ_d` (`HJO.Sym.LambdaComp`), their
reading at a negative degree (`HJO.Sym.LambdaCompInt`), and what it is for an endomorphism of `Λ`
to shift degree by `c ∈ ℤ` (`HJO.Sym.ShiftsDegree`). This
file builds the completion `Λ̂` those shifts extend to.

Mellit's Section 3.7 needs the completion because the conjugate shift `τ^*` does not act on `Λ`:
`f ↦ f·Exp[-X/M]` has a contribution in every degree. This file is the completion, the extension of
a degree shift to it, `τ^*` itself, and the three of the section's four propositions that follow
from those.

## Main definitions

* `HJO.Sym.LambdaHat`: families `(f_d)_{d ≥ 0}` with
  `f_d ∈ Λ_d`, with componentwise addition and `𝕜`-action and the convolution product.
* `HJO.Sym.lambdaComponent` — the `d`-th graded component of a symmetric function, and
  `HJO.Sym.toLambdaHat`, the family of all of them, which is the map usually written
  `f ↦ (f_d)_{d ≥ 0}` and left unnamed.
* `HJO.Sym.completionExtension`: for `D` shifting
  degree by `c`, the endomorphism `D̂` of `Λ̂` whose `e`-th member is `D(f_{e-c})`.
* `HJO.Sym.plethNegDivM` and `HJO.Sym.expNegDivM` — the substitution `f ↦ f[-X/M]` and the element
  `Exp[-X/M]` of the completion. **Neither is defined earlier**; the section below derives both
  from the conventions already fixed.
* `HJO.Sym.nsShiftStar`, `τ^*(f) = f·Exp[-X/M]`, and
  `HJO.Sym.nsShiftComp`, the composite `τ^*τ` in which it always occurs.

## Main results

* `HJO.Sym.toLambdaHat_apply`: `D̂` applied to
  the components of `f` gives the components of `D f`, so `D̂` really does extend `D`.
* `HJO.Sym.completionExtension_mul`,
  `(DD')^ = D̂ D̂'`.
* `HJO.Sym.nsShiftComp_injective`.
* `HJO.Sym.nsShiftComp_eq_of_eq` and `HJO.Sym.nsShiftComp_mul`, which are formal consequences of the
  previous three.

## The edge case the proof passes over

`HJO.Sym.completionExtension_mul` is stated for arbitrary `c, c' ∈ ℤ`, and its proof compares the
two sides "under the same condition". The conditions are not the same: at `c = 5`, `c' = -5` and
`e = 0` the left side reads `(DD')(f_0)`, which its own condition `c + c' ≤ e` admits, while the
right side is `0` because `e - c < 0`. The two agree anyway, but only because `D'` shifts degree:
`D'(f_0) ∈ Λ_{-5}`, which is the zero subspace. So that case is discharged below from
`HJO.Sym.ShiftsDegree` rather than from the arithmetic.

## Why the ring axioms of `Λ̂` are still not proved here

`HJO.Sym.LambdaHat` names three operations and all three are defined, but it asserts nothing about
them, and nothing below needs an axiom. That includes the one place where the usual argument says it
does: the injectivity behind `HJO.Sym.nsShiftComp_injective` is usually justified by `Exp[-X/M]`
"having constant term `1`, hence being a unit of the completion, so that multiplication by it is
injective". Being a unit is strictly more than the conclusion needs.
`HJO.Sym.LambdaHat.eq_zero_of_mul_eq_zero` gets injectivity from the constant term directly, by
induction on the degree: in `(HF)_d = ∑_{e ≤ d} H_e F_{d-e}` every term below `d` vanishes by the
inductive hypothesis, leaving `H_d F_0 = H_d`. No inverse is constructed, and the associativity of
the convolution — which is what an inverse would need and the only laborious axiom — is never read.
So the axioms are not proved here, no statement of this file requiring them.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Sym

section CommRingBase

variable {K : Type*} [CommRing K]

/-! ### The graded components of a symmetric function -/

/-- The `d`-th graded component of a symmetric function: the part of `f` whose monomials have
generator weights summing to `d`, where the generator `i`, standing for `p_{i+1}`, has weight
`i + 1`. -/
noncomputable def lambdaComponent (K : Type*) [CommRing K] (d : ℕ) :
    Lambda K →ₗ[K] Lambda K :=
  weightedHomogeneousComponent (fun i => i + 1) d

theorem lambdaComponent_apply (K : Type*) [CommRing K] (d : ℕ) (f : Lambda K) :
    lambdaComponent K d f = weightedHomogeneousComponent (fun i => i + 1) d f := rfl

theorem lambdaComponent_mem (K : Type*) [CommRing K] (d : ℕ) (f : Lambda K) :
    lambdaComponent K d f ∈ LambdaComp K d :=
  weightedHomogeneousComponent_mem _ f d

/-- **A homogeneous element is its own component in its own degree, and has none in any other.**
This is the uniqueness half of the grading, in the form the extension below reads it. -/
theorem lambdaComponent_of_mem {d e : ℕ} {f : Lambda K} (hf : f ∈ LambdaComp K d) :
    lambdaComponent K e f = if e = d then f else 0 :=
  weightedHomogeneousComponent_of_mem hf

/-- The finite set of degrees carrying a component of `f`: the weights of its monomials. -/
noncomputable def lambdaSupport (f : Lambda K) : Finset ℕ :=
  f.support.image (Finsupp.weight fun i => i + 1)

theorem lambdaComponent_eq_zero_of_notMem {f : Lambda K} {d : ℕ} (h : d ∉ lambdaSupport f) :
    lambdaComponent K d f = 0 :=
  weightedHomogeneousComponent_eq_zero_of_notMem _ f d h

/-- **A symmetric function is the sum of its graded components**,
`HJO.Sym.lambdaComp_isInternal` in the form a computation uses: a finite sum over the degrees
carrying a component. Compared monomial by monomial, the sum has exactly one term meeting each
monomial of `f`, the one at that monomial's weight. -/
theorem sum_lambdaComponent (f : Lambda K) :
    ∑ d ∈ lambdaSupport f, lambdaComponent K d f = f := by
  classical
  ext m
  rw [MvPolynomial.coeff_sum]
  simp only [lambdaComponent_apply, coeff_weightedHomogeneousComponent]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · symm
    by_contra hne
    exact h (Finset.mem_image_of_mem _ (MvPolynomial.mem_support_iff.2 hne))

/-! ### The completion -/

/-- **The completion of `Λ` by degree.** `HJO.Sym.LambdaHat`: the families
`(f_d)_{d ≥ 0}` with `f_d ∈ Λ_d`, read as a dependent function into the graded pieces, so that the
degree condition is carried by the type rather than by a side hypothesis.

Componentwise addition and the `𝕜`-action are the ones a product of submodules already has; the
product is the convolution `(fg)_d = ∑_{e ≤ d} f_e g_{d-e}` of
`HJO.Sym.LambdaHat.coe_mul`. -/
@[hjo "def_lambda_completion"]
abbrev LambdaHat (K : Type*) [CommRing K] : Type _ := ∀ d : ℕ, LambdaComp K d

namespace LambdaHat

/-- Two families agree when their members do. -/
@[ext]
theorem ext {F G : LambdaHat K} (h : ∀ d, (F d : Lambda K) = (G d : Lambda K)) : F = G :=
  funext fun d => Subtype.ext (h d)

theorem coe_add (F G : LambdaHat K) (d : ℕ) :
    ((F + G) d : Lambda K) = (F d : Lambda K) + (G d : Lambda K) := rfl

theorem coe_sub (F G : LambdaHat K) (d : ℕ) :
    ((F - G) d : Lambda K) = (F d : Lambda K) - (G d : Lambda K) := rfl

theorem coe_smul (r : K) (F : LambdaHat K) (d : ℕ) :
    ((r • F) d : Lambda K) = r • (F d : Lambda K) := rfl

theorem coe_zero (d : ℕ) : ((0 : LambdaHat K) d : Lambda K) = 0 := rfl

/-- **The convolution product of `HJO.Sym.LambdaHat`**: `(FG)_d = ∑_{e = 0}^{d} F_e G_{d-e}`,
a sum over the finite index set `{0, …, d}` each of whose terms lies in `Λ_d` because
`e + (d - e) = d`. -/
noncomputable instance : Mul (LambdaHat K) where
  mul F G := fun d => ⟨∑ e ∈ range (d + 1), (F e : Lambda K) * (G (d - e) : Lambda K),
    Submodule.sum_mem _ fun e he => by
      have h := mul_mem_lambdaComp (F e).2 (G (d - e)).2
      rw [Finset.mem_range] at he
      rwa [show e + (d - e) = d from by omega] at h⟩

theorem coe_mul (F G : LambdaHat K) (d : ℕ) :
    ((F * G) d : Lambda K) = ∑ e ∈ range (d + 1), (F e : Lambda K) * (G (d - e) : Lambda K) := rfl

/-- The unit of the convolution product: `1` in degree `0` and `0` above it. -/
noncomputable instance : One (LambdaHat K) where
  one := fun d => ⟨if d = 0 then 1 else 0, by
    split_ifs with h
    · subst h
      exact one_mem_lambdaComp K
    · exact zero_mem _⟩

theorem coe_one (d : ℕ) : ((1 : LambdaHat K) d : Lambda K) = if d = 0 then 1 else 0 := rfl

end LambdaHat

/-- **A symmetric function read in the completion**, as its family of graded components. This is the
map usually written `f ↦ (f_d)_{d ≥ 0}` and left unnamed;
`HJO.Sym.toLambdaHat_apply` is the statement that `HJO.Sym.completionExtension` is compatible with
it. -/
noncomputable def toLambdaHat (K : Type*) [CommRing K] : Lambda K →ₗ[K] LambdaHat K where
  toFun f := fun d => ⟨lambdaComponent K d f, lambdaComponent_mem K d f⟩
  map_add' f g := LambdaHat.ext fun d => by
    change lambdaComponent K d (f + g) = lambdaComponent K d f + lambdaComponent K d g
    exact map_add (lambdaComponent K d) f g
  map_smul' r f := LambdaHat.ext fun d => by
    change lambdaComponent K d (r • f) = r • lambdaComponent K d f
    exact map_smul (lambdaComponent K d) r f

theorem coe_toLambdaHat_apply (f : Lambda K) (d : ℕ) :
    ((toLambdaHat K f) d : Lambda K) = lambdaComponent K d f := rfl

/-! ### The extension of a degree shift to the completion -/

/-- The underlying family of `HJO.Sym.completionExtension`, before the degree condition on its
members is checked: the `e`-th member is `D(F_{e-c})` when `e - c ≥ 0`, and `0` otherwise. -/
noncomputable def extVal (c : ℤ) (D : Module.End K (Lambda K)) (F : LambdaHat K) (e : ℕ) :
    Lambda K :=
  if c ≤ (e : ℤ) then D (F ((e : ℤ) - c).toNat : Lambda K) else 0

/-- **The `e`-th member at a witnessed index.** Supplying an `n` with `n + c = e` is how every
statement below reads `HJO.Sym.extVal`, which keeps the truncated subtraction out of the
arguments. -/
theorem extVal_of_add_eq (c : ℤ) (D : Module.End K (Lambda K)) (F : LambdaHat K) {e n : ℕ}
    (hn : (n : ℤ) + c = (e : ℤ)) : extVal c D F e = D (F n : Lambda K) := by
  rw [extVal]
  split_ifs with h
  · rw [show ((e : ℤ) - c).toNat = n from by omega]
  · exact absurd hn (by omega)

/-- **The `e`-th member vanishes when no index maps to `e`**, which for a shift by `c` is exactly
`e < c`. -/
theorem extVal_of_lt (c : ℤ) (D : Module.End K (Lambda K)) (F : LambdaHat K) {e : ℕ}
    (he : (e : ℤ) < c) : extVal c D F e = 0 := by
  rw [extVal]
  split_ifs with h
  · exact absurd h (by omega)
  · rfl

theorem extVal_mem {c : ℤ} {D : Module.End K (Lambda K)} (hD : ShiftsDegree c D)
    (F : LambdaHat K) (e : ℕ) : extVal c D F e ∈ LambdaComp K e := by
  rw [extVal]
  split_ifs with hc
  · set n := ((e : ℤ) - c).toNat with hn
    have h := hD n _ (F n).2
    rw [show (n : ℤ) + c = (e : ℤ) from by omega, lambdaCompInt_natCast] at h
    exact h
  · exact zero_mem _

/-- **The extension to the completion.** `HJO.Sym.completionExtension`: for `D`
shifting degree by `c`, the `𝕜`-linear endomorphism `D̂` of `Λ̂` sending `(f_d)_{d ≥ 0}` to the
family whose `e`-th member is `D(f_{e-c})` when `e - c ≥ 0` and `0` otherwise.

The hypothesis `hD` is what makes the value a family of the right degrees — `D(f_{e-c}) ∈ Λ_e` is
`ShiftsDegree` read at `e - c` — and it is an argument rather than a typeclass because the
extension of one `D` at two different `c` is nowhere below. -/
@[hjo "def_completion_extension"]
noncomputable def completionExtension {c : ℤ} {D : Module.End K (Lambda K)}
    (hD : ShiftsDegree c D) : Module.End K (LambdaHat K) where
  toFun F := fun e => ⟨extVal c D F e, extVal_mem hD F e⟩
  map_add' F G := LambdaHat.ext fun e => by
    change extVal c D (F + G) e = extVal c D F e + extVal c D G e
    rw [extVal, extVal, extVal]
    split_ifs
    · change D ((F _ : Lambda K) + (G _ : Lambda K)) = _
      rw [map_add]
    · rw [add_zero]
  map_smul' r F := LambdaHat.ext fun e => by
    change extVal c D (r • F) e = r • extVal c D F e
    rw [extVal, extVal]
    split_ifs
    · change D (r • (F _ : Lambda K)) = _
      rw [map_smul]
    · rw [smul_zero]

theorem coe_completionExtension_apply {c : ℤ} {D : Module.End K (Lambda K)}
    (hD : ShiftsDegree c D) (F : LambdaHat K) (e : ℕ) :
    ((completionExtension hD F) e : Lambda K) = extVal c D F e := rfl

/-! ### The extension extends -/

/-- **The `e`-th component of `D f`, for `D` shifting degree by `c`.** The whole content of
`HJO.Sym.toLambdaHat_apply`: decompose `f` into its components, note that `D` carries the one
in degree `d` into `Λ_{d+c}`, and read off the component of the resulting sum in degree `e` — at
most one summand contributes, the one with `d + c = e`, and it is absent exactly when `e - c < 0`,
since `d ≥ 0`. -/
theorem lambdaComponent_apply_of_shiftsDegree {c : ℤ} {D : Module.End K (Lambda K)}
    (hD : ShiftsDegree c D) (f : Lambda K) (e : ℕ) :
    lambdaComponent K e (D f) = extVal c D (toLambdaHat K f) e := by
  classical
  have hterm : ∀ d : ℕ, lambdaComponent K e (D (lambdaComponent K d f))
      = if (d : ℤ) + c = (e : ℤ) then D (lambdaComponent K d f) else 0 := by
    intro d
    have h := hD d _ (lambdaComponent_mem K d f)
    rcases lt_or_ge ((d : ℤ) + c) 0 with hlt | hge
    · rw [eq_zero_of_mem_lambdaCompInt hlt h, map_zero]
      have hne : ¬((d : ℤ) + c = (e : ℤ)) := by omega
      simp [hne]
    · obtain ⟨p, hp⟩ : ∃ p : ℕ, (d : ℤ) + c = (p : ℤ) :=
        ⟨((d : ℤ) + c).toNat, (Int.toNat_of_nonneg hge).symm⟩
      rw [hp, lambdaCompInt_natCast] at h
      rw [lambdaComponent_of_mem h]
      by_cases hep : e = p
      · subst hep
        simp [hp]
      · have hne : ¬((d : ℤ) + c = (e : ℤ)) := by omega
        simp [hep, hne]
  have hDf : lambdaComponent K e (D f)
      = ∑ d ∈ lambdaSupport f, if (d : ℤ) + c = (e : ℤ) then D (lambdaComponent K d f) else 0 := by
    have h1 : D f = ∑ d ∈ lambdaSupport f, D (lambdaComponent K d f) := by
      rw [← map_sum, sum_lambdaComponent]
    rw [h1, map_sum]
    exact Finset.sum_congr rfl fun d _ => hterm d
  rw [hDf]
  by_cases hc : c ≤ (e : ℤ)
  · set n := ((e : ℤ) - c).toNat with hn
    have hne : (n : ℤ) + c = (e : ℤ) := by omega
    rw [extVal_of_add_eq c D _ hne, coe_toLambdaHat_apply]
    by_cases hmem : n ∈ lambdaSupport f
    · refine Finset.sum_eq_single_of_mem n hmem (fun d _ hdn => ?_) |>.trans ?_
      · have : ¬((d : ℤ) + c = (e : ℤ)) := by omega
        simp [this]
      · simp [hne]
    · rw [lambdaComponent_eq_zero_of_notMem hmem, map_zero]
      refine Finset.sum_eq_zero fun d hd => ?_
      have hdn : ¬((d : ℤ) + c = (e : ℤ)) := by
        intro hde
        exact hmem (by rwa [show n = d from by omega])
      simp [hdn]
  · rw [extVal_of_lt c D _ (by omega)]
    refine Finset.sum_eq_zero fun d _ => ?_
    have hdn : ¬((d : ℤ) + c = (e : ℤ)) := by omega
    simp [hdn]

/-- **The extension extends**, `HJO.Sym.toLambdaHat_apply`: the graded
components of `D f` are the members of `D̂` applied to the graded components of `f`. -/
@[hjo "lem_completion_extension_extends"]
theorem toLambdaHat_apply {c : ℤ} {D : Module.End K (Lambda K)} (hD : ShiftsDegree c D)
    (f : Lambda K) : toLambdaHat K (D f) = completionExtension hD (toLambdaHat K f) :=
  LambdaHat.ext fun e => by
    rw [coe_toLambdaHat_apply, coe_completionExtension_apply]
    exact lambdaComponent_apply_of_shiftsDegree hD f e

/-! ### The extension is multiplicative -/

/-- **The extension is multiplicative**, `HJO.Sym.completionExtension_mul`:
`(DD')^ = D̂ D̂'`. The composite shifts degree by `c + c'` (`HJO.Sym.ShiftsDegree.comp`), so the
left side is defined.

Comparing the members in degree `e` splits into the case where an index exists on both sides and
the three where one side has none; in the last of those the left side is `0` only because `D'`
shifts degree, the intermediate piece `Λ_{e-c}` being the zero subspace. -/
@[hjo "lem_completion_extension_comp"]
theorem completionExtension_mul {c c' : ℤ} {D D' : Module.End K (Lambda K)}
    (hD : ShiftsDegree c D) (hD' : ShiftsDegree c' D') :
    completionExtension (hD.comp hD') = completionExtension hD * completionExtension hD' := by
  refine LinearMap.ext fun F => LambdaHat.ext fun e => ?_
  have hlhs : (((completionExtension (hD.comp hD')) F) e : Lambda K)
      = extVal (c + c') (D * D') F e := coe_completionExtension_apply _ F e
  have hrhs : (((completionExtension hD * completionExtension hD') F) e : Lambda K)
      = extVal c D (completionExtension hD' F) e := coe_completionExtension_apply hD _ e
  rw [hlhs, hrhs]
  by_cases hc : c ≤ (e : ℤ)
  · set m := ((e : ℤ) - c).toNat with hm
    have hme : (m : ℤ) + c = (e : ℤ) := by omega
    rw [extVal_of_add_eq c D _ hme, coe_completionExtension_apply hD' F m]
    by_cases hc' : c' ≤ (m : ℤ)
    · set n := ((m : ℤ) - c').toNat with hn
      have hnm : (n : ℤ) + c' = (m : ℤ) := by omega
      rw [extVal_of_add_eq c' D' F hnm,
        extVal_of_add_eq (c + c') (D * D') F (show (n : ℤ) + (c + c') = (e : ℤ) from by omega)]
      rfl
    · rw [extVal_of_lt c' D' F (by omega), map_zero, extVal_of_lt _ _ _ (by omega)]
  · rw [extVal_of_lt c D _ (by omega)]
    by_cases hcc : c + c' ≤ (e : ℤ)
    · set n := ((e : ℤ) - (c + c')).toNat with hn
      have hne : (n : ℤ) + (c + c') = (e : ℤ) := by omega
      have hzero : D' (F n : Lambda K) = 0 :=
        eq_zero_of_mem_lambdaCompInt (show (n : ℤ) + c' < 0 from by omega) (hD' n _ (F n).2)
      rw [extVal_of_add_eq (c + c') (D * D') F hne]
      change D (D' (F n : Lambda K)) = 0
      rw [hzero, map_zero]
    · exact extVal_of_lt _ _ _ (by omega)

/-! ### Multiplication by a fixed element of the completion -/

/-- **Right multiplication distributes over a difference**, which is the only ring law the
injectivity below reads. -/
theorem LambdaHat.sub_mul (F G H : LambdaHat K) : (F - G) * H = F * H - G * H :=
  LambdaHat.ext fun d => by
    rw [LambdaHat.coe_sub, LambdaHat.coe_mul, LambdaHat.coe_mul, LambdaHat.coe_mul,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun e _ => by rw [LambdaHat.coe_sub, _root_.sub_mul]

/-- **A factor with `1` in degree zero cannot annihilate anything.** Induction on the degree: in
`(HF)_d = ∑_{e ≤ d} H_e F_{d-e}` every term with `e < d` vanishes by the inductive hypothesis, so
the whole sum is `H_d F_0 = H_d`.

This is what the usual remark that `Exp[-X/M]` "has constant term `1`, hence is a unit of the
completion" is used for, and it is strictly weaker than being a unit: no inverse is constructed and
no ring axiom beyond `HJO.Sym.LambdaHat.coe_mul` is read. In particular the associativity of the
convolution, which an inverse would need, is not required anywhere in Section 3.7. -/
theorem LambdaHat.eq_zero_of_mul_eq_zero {F H : LambdaHat K} (hF : (F 0 : Lambda K) = 1)
    (h : H * F = 0) : H = 0 := by
  refine LambdaHat.ext fun d => ?_
  rw [LambdaHat.coe_zero]
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    have hd : ((H * F) d : Lambda K) = 0 := by rw [h]; rfl
    rw [LambdaHat.coe_mul, Finset.sum_eq_single_of_mem d (Finset.self_mem_range_succ d)
      (fun e he hed => by
        rw [ih e (by rw [Finset.mem_range] at he; omega), zero_mul])] at hd
    rwa [Nat.sub_self, hF, mul_one] at hd

/-- **Right multiplication by a factor with `1` in degree zero is injective.** -/
theorem LambdaHat.mul_right_injective {F : LambdaHat K} (hF : (F 0 : Lambda K) = 1) :
    Function.Injective fun G : LambdaHat K => G * F := by
  intro G G' h
  have h' : G * F = G' * F := h
  refine sub_eq_zero.1 (LambdaHat.eq_zero_of_mul_eq_zero hF ?_)
  rw [LambdaHat.sub_mul, h', sub_self]

/-- **A symmetric function is determined by its graded components.** -/
theorem toLambdaHat_injective (K : Type*) [CommRing K] :
    Function.Injective (toLambdaHat K) := by
  intro f g h
  have hc : ∀ d, lambdaComponent K d (f - g) = 0 := fun d => by
    have hd := congrArg (fun F : LambdaHat K => (F d : Lambda K)) h
    rw [map_sub]
    simp only [coe_toLambdaHat_apply] at hd
    rw [hd, sub_self]
  refine sub_eq_zero.1 ?_
  rw [← sum_lambdaComponent (f - g), Finset.sum_eq_zero fun d _ => hc d]

end CommRingBase

/-! ### The alphabet `-X/M` and the plethystic exponential

`HJO.Sym.nsShiftStar` reads `τ^*(f) = f·Exp[-X/M]`, and neither bracket has
an earlier definition. Both are forced by the conventions already fixed.

**The alphabet.** `HJO.Sym.plethAxis` settles how a bracket whose alphabet is built from the
parameters is read: its scalar at `p_j` is `p_j` **of the alphabet**, not the `j`-th power of an
element of `𝕜` — that declaration exists precisely to reject the second reading, which also
typechecks.
`HJO.Sym.plethShift` then fixes the multiplicative half: the alphabet `M/z` of
`HJO.Sym.paramProduct` contributes `(1-q^k)(1-u^k)z^{-k}` at `p_k`, which is `p_k[M]·p_k[1/z]`. So
`p_k` is multiplicative in the alphabet under these conventions, and a quotient of alphabets
divides: `p_k[X/M] = p_k / ((1-q^k)(1-u^k))`. With `p_k` additive,
`p_k[-X/M] = -p_k/((1-q^k)(1-u^k))`, which is `HJO.Sym.plethNegDivM`.

**The exponential.** `Exp[A] = ∑_{n ≥ 0} h_n[A]`, and the definitions confirm it twice rather than
stating it: `HJO.Sym.DopInt` writes the series as `∑_{r ≥ 0}(-z)^r e_r`, which is
`∑_r h_r[-zX]` since `h_r[-A] = (-1)^r e_r[A]`; and `HJO.Sweep.dminus` names
`∑_n (-1)^n e_n y_k^{-n}` as `Exp[-y_k^{-1}X]`, the same identity at
`z = y_k^{-1}`.

Those two together give `Exp[-X/M]` as the family `(h_d[-X/M])_{d ≥ 0}`, which lies in the
completion because each `h_d` is homogeneous of degree `d` and a diagonal substitution preserves
degree. Its member in degree `0` is `h_0 = 1`, which is the property
`HJO.Sym.nsShiftComp_injective` reads.

**The one thing the conventions do not settle** is whether `𝕜` makes the scalars exist. The
substitution divides by `(1-q^k)(1-u^k)` for every `k ≥ 1`, and nothing in `HJO.Sym.nsShiftStar`
records that hypothesis. At the intended `𝕜` the two parameters satisfy no polynomial relation, so
every such factor is nonzero and the definition is harmless as stated; below, the inverse is the
field inverse, which is total, and no statement reads its value at a degenerate parameter —
`HJO.Sym.coe_expNegDivM_zero`, the only property used, is `h_0 = 1` and holds for all `q`, `u`. -/

section Exponential

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- **The substitution `f ↦ f[-X/M]`**, for `M = (1-q)(1-u)`: the `𝕜`-algebra endomorphism of `Λ`
with `p_k ↦ -p_k/((1-q^k)(1-u^k))`.

The scalar is the reciprocal of `p_k[M] = (1-q^k)(1-u^k)`, the one `HJO.Sym.plethShift` attaches to
`p_k` — *not* the `k`-th power of `M⁻¹`, which is what `HJO.Sym.plethScale` would give and what
`HJO.Sym.plethAxis` exists to rule out for brackets of this shape. -/
noncomputable def plethNegDivM (q u : K) : Lambda K →ₐ[K] Lambda K :=
  diagScale fun i => -((1 - q ^ (i + 1)) * (1 - u ^ (i + 1)))⁻¹

omit [Algebra ℚ K] in
/-- **`p_k[-X/M] = -p_k/((1-q^k)(1-u^k))`**, the defining formula read against the index convention
of `HJO.Sym.powerSum`, under which generator `i` is `p_{i+1}`. -/
theorem plethNegDivM_powerSum (q u : K) {k : ℕ} (hk : 1 ≤ k) :
    plethNegDivM q u (powerSum K k)
      = MvPolynomial.C (-((1 - q ^ k) * (1 - u ^ k))⁻¹) * powerSum K k := by
  rw [plethNegDivM, diagScale_powerSum, show k - 1 + 1 = k from by omega]

/-- **`Exp[-X/M]` as an element of the completion**: the family whose member in degree `d` is
`h_d[-X/M]`.

It is an element of `Λ̂` and not of `Λ` — which is Mellit's reason (Section 3.7) for introducing the
completion at all — because it has a nonzero member in every degree. Each member lies in the right
piece because `h_d` is homogeneous of degree `d` (`HJO.Sym.completeHomog_mem_lambdaComp`) and a
diagonal substitution preserves degree (`HJO.Sym.diagScale_mem_lambdaComp`). -/
noncomputable def expNegDivM (q u : K) : LambdaHat K := fun d =>
  ⟨plethNegDivM q u (completeHomog K d), by
    rw [plethNegDivM]
    exact diagScale_mem_lambdaComp _ (completeHomog_mem_lambdaComp K d)⟩

theorem coe_expNegDivM (q u : K) (d : ℕ) :
    (expNegDivM q u d : Lambda K) = plethNegDivM q u (completeHomog K d) := rfl

/-- **`Exp[-X/M]` has `1` in degree zero**, since `h_0 = 1` and the substitution is an algebra map.
This is the whole of what `HJO.Sym.nsShiftComp_injective` reads about it, and it holds for every `q`
and `u`. -/
theorem coe_expNegDivM_zero (q u : K) : (expNegDivM q u 0 : Lambda K) = 1 := by
  rw [coe_expNegDivM, UkRegular.completeHomog_zero K, map_one]

/-! ### The conjugate shift -/

/-- **The conjugate shift `τ^*`.** `HJO.Sym.nsShiftStar`: the `𝕜`-linear map
from `Λ` to the completion `Λ̂` with `τ^*(f) = f·Exp[-X/M]`, the product being the convolution of
`HJO.Sym.LambdaHat` and `f` being read in `Λ̂` as its family of graded components.

It does not act on `Λ`, as Mellit remarks in Section 3.7, and is harmless there because only the
injectivity of the composite `τ^*τ` is ever used. -/
@[hjo "def_mellit_ns_shift_star"]
noncomputable def nsShiftStar (q u : K) : Lambda K →ₗ[K] LambdaHat K where
  toFun f := toLambdaHat K f * expNegDivM q u
  map_add' f g := LambdaHat.ext fun d => by
    rw [LambdaHat.coe_mul, LambdaHat.coe_add, LambdaHat.coe_mul, LambdaHat.coe_mul,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [coe_toLambdaHat_apply, coe_toLambdaHat_apply, coe_toLambdaHat_apply, map_add,
      _root_.add_mul]
  map_smul' r f := LambdaHat.ext fun d => by
    rw [RingHom.id_apply, LambdaHat.coe_mul, LambdaHat.coe_smul, LambdaHat.coe_mul,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [coe_toLambdaHat_apply, coe_toLambdaHat_apply, map_smul, smul_mul_assoc]

theorem coe_nsShiftStar_apply (q u : K) (f : Lambda K) (d : ℕ) :
    ((nsShiftStar q u f) d : Lambda K)
      = ∑ e ∈ range (d + 1), lambdaComponent K e f * (expNegDivM q u (d - e) : Lambda K) := rfl

/-- **The composite `τ^*τ`**, the only shape in which the two shifts of Section 3.7 occur: `τ` adds
the single letter `1` and `τ^*` multiplies by `Exp[-X/M]`, so `τ^*τ f = f[X+1]·Exp[-X/M]`. -/
noncomputable def nsShiftComp (q u : K) : Lambda K →ₗ[K] LambdaHat K :=
  (nsShiftStar q u).comp (unitShift : Lambda K →ₐ[K] Lambda K).toLinearMap

theorem nsShiftComp_apply (q u : K) (f : Lambda K) :
    nsShiftComp q u f = nsShiftStar q u (unitShift f) := rfl

/-- **The composite shift is injective**, `HJO.Sym.nsShiftComp_injective`. Three
injections: `τ` is bijective with inverse `f ↦ f[X-1]`
(`HJO.Sym.unitShift_injective`); reading a symmetric function as its family of graded components is
injective because it is the sum of them; and multiplying by `Exp[-X/M]` is injective because that
element has `1` in degree zero.

The middle step is the one hidden in "`τ^*` is injective": `τ^*` is a composite of
two maps, and only the second reads anything about `Exp[-X/M]`. -/
@[hjo "lem_mellit_ns_injective"]
theorem nsShiftComp_injective (q u : K) : Function.Injective (nsShiftComp q u) := by
  intro f g h
  rw [nsShiftComp_apply, nsShiftComp_apply] at h
  have h1 : toLambdaHat K (unitShift f) * expNegDivM q u
      = toLambdaHat K (unitShift g) * expNegDivM q u := h
  exact unitShift_injective
    (toLambdaHat_injective K (LambdaHat.mul_right_injective (coe_expNegDivM_zero q u) h1))

/-! ### What the composite shift determines -/

/-- **The shifted operator is unique**, `HJO.Sym.nsShiftComp_eq_of_eq`: for `D` shifting
degree by `c`, at most one endomorphism `E` of `Λ` satisfies `τ^*τE = D̂τ^*τ`. Immediately from the
injectivity of `τ^*τ`; the hypothesis `hD` is read only to name `D̂`. -/
@[hjo "lem_mellit_ns_unique"]
theorem nsShiftComp_eq_of_eq (q u : K) {c : ℤ} {D : Module.End K (Lambda K)}
    (hD : ShiftsDegree c D) {E E' : Module.End K (Lambda K)}
    (hE : ∀ f, nsShiftComp q u (E f) = completionExtension hD (nsShiftComp q u f))
    (hE' : ∀ f, nsShiftComp q u (E' f) = completionExtension hD (nsShiftComp q u f)) :
    E = E' :=
  LinearMap.ext fun f => nsShiftComp_injective q u ((hE f).trans (hE' f).symm)

/-- **The shift is multiplicative where it is defined**,
`HJO.Sym.nsShiftComp_mul`: if `E_1` and `E_2` are transported by `D_1` and `D_2`, then `E_1E_2`
is transported by `D_1D_2`.

Three rewrites — the hypothesis on `E_1`, then the one on `E_2`, then
`HJO.Sym.completionExtension_mul` to fuse the two extensions — and the composite shifts degree by
`c_1 + c_2` by `HJO.Sym.ShiftsDegree.comp`, which is what makes the fused extension exist. -/
@[hjo "lem_mellit_ns_multiplicative"]
theorem nsShiftComp_mul (q u : K) {c₁ c₂ : ℤ} {D₁ D₂ : Module.End K (Lambda K)}
    (hD₁ : ShiftsDegree c₁ D₁) (hD₂ : ShiftsDegree c₂ D₂) {E₁ E₂ : Module.End K (Lambda K)}
    (hE₁ : ∀ f, nsShiftComp q u (E₁ f) = completionExtension hD₁ (nsShiftComp q u f))
    (hE₂ : ∀ f, nsShiftComp q u (E₂ f) = completionExtension hD₂ (nsShiftComp q u f))
    (f : Lambda K) :
    nsShiftComp q u ((E₁ * E₂) f)
      = completionExtension (hD₁.comp hD₂) (nsShiftComp q u f) := by
  have hfuse := completionExtension_mul hD₁ hD₂
  change nsShiftComp q u (E₁ (E₂ f)) = _
  rw [hE₁ (E₂ f), hE₂ f, hfuse]
  rfl

end Exponential

end HJO.Sym

end
