/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.PowerSeries.Basic
public import HJO.Symmetric.SymmetricFunctions
public meta import HJO.Attr

/-! # The parameter involution, the displacements and the kernel of the Carlsson--Mellit layer

The Hall--Littlewood half of the Carlsson--Mellit layer works with six operations on the ring of
symmetric functions, all of them determined by their values on the power sums, and none of them in
`Mathlib`. This file defines them and records the identities that characterise each:

* `cj : f ↦ f̄`, inverting the parameters of the base while fixing every power sum;
* `ω₋ : f ↦ f[-X]`, negating the alphabet;
* `β : f ↦ f[X - (q-1)/z]` and `β' : f ↦ f[X - (q-1)/w]`, the two displacements;
* `κ_r`, the kernel coefficients produced when two displacements are composed;
* `Ω(t) = ∑ (-1)ⁿ eₙ tⁿ`, the alternating elementary series;
* `e_α`, the elementary symmetric function of a composition.

## Main definitions

* `HJO.Sym.paramInvLambda`, `HJO.Sym.paramInvSeries`: the parameter involution on `Λ` and on `P`.
* `HJO.Sym.plethNegate`: `ω₋`.
* `HJO.Sym.plethHallLittlewood`: `β`.
* `HJO.Sym.plethShiftW`: `β'`.
* `HJO.Sym.bkernel`: `κ_r`.
* `HJO.Sym.elemSymmSeries`: `Ω(t)`.
* `HJO.Sym.elemSymmComp`: `e_α`.

## Implementation notes

The involution `cj` inverts the two parameters of `𝕂 = ℚ(q, u)`, an automorphism that exists only
at that field — over a general base ring, even at an algebraically independent pair, `q ↦ q⁻¹` is
not defined. So `paramInvLambda` carries the automorphism of the base as an argument: it is stated
for an arbitrary `σ : K ≃+* K`, and `cj` is the instance at the inversion. Nothing
else in this file needs a parameter automorphism, so everything else is over a commutative ring,
with `q` a ring element.

`β` has target `Polynomial (Lambda K)` in the variable `w = z⁻¹`, following
`HJO.Sym.plethShift`: the ring `Λ[z, z⁻¹]` receives only the non-negative powers of `z⁻¹`, so
the polynomial ring in `z⁻¹` is where the image actually lies, and extraction of the coefficient
of a power of `z` from a product with a power series in `z` becomes a finite sum. `β'` instead has
target `LaurentPolynomial (Lambda K)`, the ring `Λ[w, w⁻¹]` verbatim, because its consumer is
the two-variable ring `𝒵`, in which both variables are inverted; the two maps are therefore not
the same declaration even though each sends `p_k` to `p_k + (1 - q^k)` times the inverse `k`-th
power of its own variable.

`ω₋` is *not* the scaling `HJO.Sym.plethScale (-1)`: the latter attaches `(-1)^k` to `p_k` and the
former attaches `-1`, and the two differ at every even `k` as soon as `2 ≠ 0` in the base. The
plethystic bracket notation `f[-X]` invites exactly that confusion.

`κ_r` satisfies `κ_{r+1} = q κ_r` for `r ≥ 1` but not at `r = 0`, and that single failure is what
makes the telescoping computations of the layer collapse to two terms;
`bkernel_succ_succ` and `bkernel_one_ne` record both halves.

## References

This file formalises the definitions `HJO.Sym.paramInvLambda`, `HJO.Sym.plethNegate`,
`HJO.Sym.plethHallLittlewood`, `HJO.Sym.plethShiftW`, `HJO.Sym.bkernel`, `HJO.Sym.elemSymmSeries`
and `HJO.Sym.elemSymmComp`.
-/

@[expose] public section

namespace HJO.Sym

/-! ### Inverting the parameters of the base -/

section ParamInv

variable {K : Type*} [CommRing K]

/-- **Inverting the parameters** on `Λ`: the map `cj : f ↦ f̄`, the ring automorphism of
`Lambda K` that fixes every power sum `p_k` and moves the coefficient of each power-sum monomial
by the automorphism `σ` of the base. For `K = ℚ(q, u)` and `σ` the inversion `q ↦ q⁻¹`,
`u ↦ u⁻¹`, this is the `cj`. It is `σ`-semilinear and not `K`-linear. -/
@[hjo "def_cm_bar"]
noncomputable def paramInvLambda (σ : K ≃+* K) : Lambda K ≃+* Lambda K :=
  MvPolynomial.mapEquiv ℕ σ

@[simp]
theorem paramInvLambda_apply (σ : K ≃+* K) (f : Lambda K) :
    paramInvLambda σ f = MvPolynomial.map (σ : K →+* K) f :=
  MvPolynomial.mapEquiv_apply ℕ σ f

/-- **`cj` acts on coefficients by `σ`**: the coefficient of a power-sum monomial in `f̄` is the
image under `σ` of its coefficient in `f`. -/
@[hjo "def_cm_bar", simp]
theorem coeff_paramInvLambda (σ : K ≃+* K) (f : Lambda K) (d : ℕ →₀ ℕ) :
    MvPolynomial.coeff d (paramInvLambda σ f) = σ (MvPolynomial.coeff d f) := by
  rw [paramInvLambda_apply, MvPolynomial.coeff_map]
  rfl

/-- `cj` moves a scalar by `σ`; this is the conjugation `c ↦ c̄`, read inside `Λ`. -/
@[simp]
theorem paramInvLambda_C (σ : K ≃+* K) (c : K) :
    paramInvLambda σ (MvPolynomial.C c) = MvPolynomial.C (σ c) := by
  rw [paramInvLambda_apply, MvPolynomial.map_C]
  rfl

/-- `cj` fixes the generator `i` of `Lambda K`, which stands for `p_{i+1}`. -/
@[simp]
theorem paramInvLambda_X (σ : K ≃+* K) (i : ℕ) :
    paramInvLambda σ (MvPolynomial.X i) = MvPolynomial.X i := by
  rw [paramInvLambda_apply, MvPolynomial.map_X]

/-- **`cj` fixes each power sum**: `p̄_k = p_k`, for every `k`. -/
@[hjo "def_cm_bar"]
theorem paramInvLambda_powerSum (σ : K ≃+* K) (k : ℕ) :
    paramInvLambda σ (powerSum K k) = powerSum K k := by
  rw [powerSum, paramInvLambda_X]

/-- The inverse of `cj` is the `cj` of the inverse automorphism of the base. -/
@[simp]
theorem paramInvLambda_symm (σ : K ≃+* K) :
    (paramInvLambda σ).symm = paramInvLambda σ.symm := rfl

/-- **Inverting the parameters** on `P = 𝕂⟦x₁, x₂, …⟧`: the map `g ↦ ḡ`, the ring automorphism of
`AlphabetSeries K` moving the coefficient of each monomial in the alphabet by the automorphism `σ`
of the base and fixing the alphabet itself. -/
@[hjo "def_cm_bar"]
noncomputable def paramInvSeries (σ : K ≃+* K) : AlphabetSeries K ≃+* AlphabetSeries K :=
  RingEquiv.ofRingHom (MvPowerSeries.map (σ : K →+* K)) (MvPowerSeries.map (σ.symm : K →+* K))
    (by ext g d; simp) (by ext g d; simp)

@[simp]
theorem paramInvSeries_apply (σ : K ≃+* K) (g : AlphabetSeries K) :
    paramInvSeries σ g = MvPowerSeries.map (σ : K →+* K) g := rfl

/-- **The bar on `P` acts on coefficients by `σ`**: the coefficient of a monomial in the alphabet
in `ḡ` is the image under `σ` of its coefficient in `g`. -/
@[hjo "def_cm_bar", simp]
theorem coeff_paramInvSeries (σ : K ≃+* K) (g : AlphabetSeries K) (d : ℕ →₀ ℕ) :
    MvPowerSeries.coeff d (paramInvSeries σ g) = σ (MvPowerSeries.coeff d g) := by
  rw [paramInvSeries_apply, MvPowerSeries.coeff_map]
  rfl

/-- The inverse of the bar on `P` is the bar of the inverse automorphism of the base. -/
@[simp]
theorem paramInvSeries_symm (σ : K ≃+* K) :
    (paramInvSeries σ).symm = paramInvSeries σ.symm := rfl

end ParamInv

/-! ### Negating the alphabet -/

/-- **Negating the alphabet**: the substitution `ω₋ : f ↦ f[-X]` by the virtual alphabet `-X`,
the `K`-algebra endomorphism of `Lambda K` sending the power sum `p_k` to `-p_k` for every `k`.
Power sums being additive in the alphabet, the scalar is `-1` at every `k`, and not the power
`(-1) ^ k` that `plethScale (-1)` contributes; the two scalars differ at every even `k`, and the
two maps differ there as soon as `2 ≠ 0` in `K`. -/
@[hjo "def_cm_negate"]
noncomputable def plethNegate (K : Type*) [CommRing K] : Lambda K →ₐ[K] Lambda K :=
  diagScale fun _ => (-1 : K)

/-- Negating the alphabet negates the generator `i` of `Lambda K`, which stands for `p_{i+1}`. -/
@[simp]
theorem plethNegate_X (K : Type*) [CommRing K] (i : ℕ) :
    plethNegate K (MvPolynomial.X i) = -MvPolynomial.X i := by
  rw [plethNegate, diagScale_X]
  simp

/-- **The defining property of `ω₋`**: negating the alphabet sends the power sum `p_k` to `-p_k`,
with the scalar `-1` at every `k` rather than the `k`-th power `(-1) ^ k` of the scaling
`plethScale (-1)`. -/
@[hjo "def_cm_negate"]
theorem plethNegate_powerSum (K : Type*) [CommRing K] (k : ℕ) :
    plethNegate K (powerSum K k) = -powerSum K k := by
  rw [powerSum, plethNegate_X]

/-! ### The two displacements -/

/-- **The Hall--Littlewood displacement** `β : f ↦ f[X - (q - 1)/z]`: the `K`-algebra
homomorphism from `Lambda K` to `Polynomial (Lambda K)` sending the power sum `p_k` to
`p_k + (1 - q ^ k) z⁻ᵏ`. The displacing alphabet `q - 1` is a difference of one-letter alphabets,
so the scalar is the virtual difference `1 - q ^ k` and not `-(q - 1) ^ k`. Its target is the
polynomial ring in `w = z⁻¹`, only non-negative powers of `w` occurring. -/
@[hjo "def_cm_bshift"]
noncomputable def plethHallLittlewood {K : Type*} [CommRing K] (q : K) :
    Lambda K →ₐ[K] Polynomial (Lambda K) :=
  MvPolynomial.aeval fun i => Polynomial.C (powerSum K (i + 1)) +
    Polynomial.C (MvPolynomial.C (1 - q ^ (i + 1))) * Polynomial.X ^ (i + 1)

/-- **The displacement in the second variable** `β' : f ↦ f[X - (q - 1)/w]`: the `K`-algebra
homomorphism from `Lambda K` to `LaurentPolynomial (Lambda K) = Λ[w, w⁻¹]` sending the power sum
`p_k` to `p_k + (1 - q ^ k) w⁻ᵏ`. Unlike `plethHallLittlewood`, whose target is written in the
inverted variable and is therefore an honest polynomial ring, this one keeps the
two-sided Laurent ring `Λ[w, w⁻¹]`, because its consumer is the two-variable ring
`𝒵 = Λ[[z]][z⁻¹][[w]][w⁻¹]`, in which `w` itself is inverted. -/
@[hjo "def_cm_bshift_w"]
noncomputable def plethShiftW {K : Type*} [CommRing K] (q : K) :
    Lambda K →ₐ[K] LaurentPolynomial (Lambda K) :=
  MvPolynomial.aeval fun i => LaurentPolynomial.C (powerSum K (i + 1)) +
    LaurentPolynomial.C (MvPolynomial.C (1 - q ^ (i + 1))) * LaurentPolynomial.T (-(i + 1 : ℤ))

section Displacement

variable {K : Type*} [CommRing K]

/-- The Hall--Littlewood displacement on the generator `i` of `Lambda K`, which stands for
`p_{i+1}`. -/
@[simp]
theorem plethHallLittlewood_X (q : K) (i : ℕ) :
    plethHallLittlewood q (MvPolynomial.X i) = Polynomial.C (powerSum K (i + 1)) +
      Polynomial.C (MvPolynomial.C (1 - q ^ (i + 1))) * Polynomial.X ^ (i + 1) := by
  rw [plethHallLittlewood, MvPolynomial.aeval_X]

/-- **The defining property of `β`**: the Hall--Littlewood displacement sends the power sum `p_k`
to `p_k + (1 - q ^ k) z⁻ᵏ` for every `k ≥ 1`, the inclusion `Λ → Λ[w]` being `Polynomial.C` and
`w` being `z⁻¹`. -/
@[hjo "def_cm_bshift"]
theorem plethHallLittlewood_powerSum (q : K) {k : ℕ} (hk : 0 < k) :
    plethHallLittlewood q (powerSum K k) = Polynomial.C (powerSum K k) +
      Polynomial.C (MvPolynomial.C (1 - q ^ k)) * Polynomial.X ^ k := by
  rw [powerSum, plethHallLittlewood_X, Nat.sub_add_cancel hk, powerSum]

/-- The Hall--Littlewood displacement of a constant is that constant. -/
@[simp]
theorem plethHallLittlewood_C (q : K) (a : K) :
    plethHallLittlewood q (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) := by
  rw [plethHallLittlewood, MvPolynomial.aeval_C, Polynomial.algebraMap_apply,
    MvPolynomial.algebraMap_eq]

/-- The Hall--Littlewood displacement is the plethystic displacement `HJO.Sym.plethShift` at
`u = 0`: the scalar `(1 - q ^ k)(1 - u ^ k)` becomes `1 - q ^ k` for every `k ≥ 1`. The two are
different maps over the field `ℚ(q, u)`, where `u` is a free parameter, so this is an
identity over a base ring in which `u` may be specialised, and it is how the identities proved
for `plethShift` — and the operators `HJO.Sym.Dop q 0 r` — apply to `β`. -/
theorem plethHallLittlewood_eq_plethShift (q : K) : plethHallLittlewood q = plethShift q 0 := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [plethHallLittlewood_X, plethShift, MvPolynomial.aeval_X, zero_pow i.succ_ne_zero, sub_zero,
    mul_one]

/-- The second displacement on the generator `i` of `Lambda K`, which stands for `p_{i+1}`. -/
@[simp]
theorem plethShiftW_X (q : K) (i : ℕ) :
    plethShiftW q (MvPolynomial.X i) = LaurentPolynomial.C (powerSum K (i + 1)) +
      LaurentPolynomial.C (MvPolynomial.C (1 - q ^ (i + 1))) *
        LaurentPolynomial.T (-(i + 1 : ℤ)) := by
  rw [plethShiftW, MvPolynomial.aeval_X]

/-- **The defining property of `β'`**: the second displacement sends the power sum `p_k` to
`p_k + (1 - q ^ k) w⁻ᵏ` for every `k ≥ 1`, in the Laurent ring `Λ[w, w⁻¹]`. -/
@[hjo "def_cm_bshift_w"]
theorem plethShiftW_powerSum (q : K) {k : ℕ} (hk : 0 < k) :
    plethShiftW q (powerSum K k) = LaurentPolynomial.C (powerSum K k) +
      LaurentPolynomial.C (MvPolynomial.C (1 - q ^ k)) * LaurentPolynomial.T (-(k : ℤ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hX : powerSum K (m + 1) = MvPolynomial.X m := by rw [powerSum, Nat.add_sub_cancel]
  have hT : (-((m : ℤ) + 1)) = -((m + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [hX, plethShiftW_X, hX, hT]

/-- The second displacement of a constant is that constant. -/
@[simp]
theorem plethShiftW_C (q : K) (a : K) :
    plethShiftW q (MvPolynomial.C a) = LaurentPolynomial.C (MvPolynomial.C a) := by
  rw [plethShiftW, MvPolynomial.aeval_C]
  rfl

end Displacement

/-! ### The kernel coefficients -/

section Kernel

variable {K : Type*} [CommRing K]

/-- **The kernel coefficients** `κ_r`: `1` at `r = 0` and `q^{r-1}(q - 1)` for `r ≥ 1`. These are
the coefficients of the expansion of `(1 - t)/(1 - qt)` in powers of `t`, which is the kernel
produced when two of the displacements are composed. -/
@[hjo "def_cm_bkernel"]
def bkernel (q : K) (r : ℕ) : K :=
  if r = 0 then 1 else q ^ (r - 1) * (q - 1)

/-- The zeroth kernel coefficient is `1`. -/
@[hjo "def_cm_bkernel", simp]
theorem bkernel_zero (q : K) : bkernel q 0 = 1 := by
  simp [bkernel]

/-- The kernel coefficients at a positive index: `κ_{r+1} = q^r (q - 1)`, that is
`κ_r = q^{r-1}(q-1)` for `r ≥ 1`, with nothing truncated. -/
@[hjo "def_cm_bkernel", simp]
theorem bkernel_succ (q : K) (r : ℕ) : bkernel q (r + 1) = q ^ r * (q - 1) := by
  simp [bkernel]

/-- The kernel coefficients are geometric from the index `1` on: `κ_{r+1} = q κ_r` for `r ≥ 1`. -/
theorem bkernel_succ_succ (q : K) (r : ℕ) : bkernel q (r + 2) = q * bkernel q (r + 1) := by
  rw [bkernel_succ, bkernel_succ, pow_succ]
  ring

/-- The geometric recursion fails at the first step: `κ_1 = q - 1` while `q κ_0 = q`, and the two
differ as soon as `1 ≠ 0` in `K`. That single failure is what makes the telescoping computations of
the layer collapse to two terms. -/
theorem bkernel_one_ne (q : K) (h : (1 : K) ≠ 0) : bkernel q 1 ≠ q * bkernel q 0 := by
  rw [bkernel_succ, bkernel_zero, pow_zero, one_mul, mul_one]
  exact fun hq => h (sub_eq_self.mp hq)

end Kernel

/-! ### The alternating elementary series and the elementary functions of a composition -/

section Elementary

variable (K : Type*) [CommRing K] [Algebra ℚ K]

/-- **The alternating elementary series** `Ω(t) = ∑_{n ≥ 0} (-1)^n e_n t^n`, an element of
`Λ[[t]]`. The `∑_n (-z)^n e_n` is this series at `t = z`, and the lowering operators
of the layer are the coefficient extractions from a product with it. -/
@[hjo "def_cm_bsign_series"]
noncomputable def elemSymmSeries : PowerSeries (Lambda K) :=
  PowerSeries.mk fun n => (-1) ^ n * elemSymm K n

/-- **The coefficients of `Ω(t)`**: the coefficient of `t^n` is `(-1)^n e_n`. -/
@[hjo "def_cm_bsign_series", simp]
theorem coeff_elemSymmSeries (n : ℕ) :
    PowerSeries.coeff n (elemSymmSeries K) = (-1) ^ n * elemSymm K n :=
  PowerSeries.coeff_mk n _

/-- The constant term of `Ω(t)` is `1`, since `e_0 = 1`. -/
@[simp]
theorem constantCoeff_elemSymmSeries : PowerSeries.constantCoeff (elemSymmSeries K) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_elemSymmSeries]
  rw [elemSymm, pow_zero, one_mul]

/-- **The elementary symmetric function of a composition** `e_α = e_{α_1} e_{α_2} ⋯ e_{α_ℓ}`, the
empty product being `1`. The composition is recorded as the list of its parts, which is the
`blocks` of a `Composition`; the order of the parts is visible, as the descent-set consumers
need, and the empty product is `1` by definition of `List.prod`. -/
@[hjo "def_om_esymm_comp"]
noncomputable def elemSymmComp (α : List ℕ) : Lambda K :=
  (α.map (elemSymm K)).prod

/-- `e_α` of the empty composition is `1`, the empty product. -/
@[hjo "def_om_esymm_comp", simp]
theorem elemSymmComp_nil : elemSymmComp K [] = 1 := rfl

/-- `e_α` splits off its first part: `e_{(a, α)} = e_a e_α`. Together with `elemSymmComp_nil` this
is the product formula, read by induction on the list of parts. -/
@[hjo "def_om_esymm_comp", simp]
theorem elemSymmComp_cons (a : ℕ) (α : List ℕ) :
    elemSymmComp K (a :: α) = elemSymm K a * elemSymmComp K α := by
  rw [elemSymmComp, elemSymmComp, List.map_cons, List.prod_cons]

/-- A value check: `e_{(2, 1)} = e_2 e_1`, a product of two factors in the order the composition
lists them. -/
theorem elemSymmComp_pair (a b : ℕ) :
    elemSymmComp K [a, b] = elemSymm K a * elemSymm K b := by
  rw [elemSymmComp_cons, elemSymmComp_cons, elemSymmComp_nil, mul_one]

end Elementary

end HJO.Sym
