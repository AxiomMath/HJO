/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Ascent.Transport
public import HJO.Collinear.HAlphabet
public import HJO.CreationSeeds.Basic
public import HJO.Symmetric.AxisSub
public import HJO.Defs
public meta import HJO.Attr

/-!
# Transport of the axis generators, the creation operators and the alphabet series

Let `φ : K →ₐ[ℚ] K'` be a homomorphism of fields of characteristic zero. This file shows that the
coefficient extension along `φ` commutes with the diagonal substitutions, the virtual axis
alphabet, the axis generators and the axis substitution, with the creation displacement and the
creation operators together with their composites, and, on the power series in the alphabet
`x₁, x₂, …`, fixes Gessel's fundamental quasisymmetric functions and is compatible with any two
realisations of the symmetric functions.

## Main definitions

* `alphabetMap`: The coefficientwise map `K⟦x₁, x₂, …⟧ → K'⟦x₁, x₂, …⟧` induced by `φ`.

## Main results

* `lambdaMap_axisSub`: The coefficient extension commutes with the axis substitution.
* `axisSub_bijective_of_isAdmissible`: At an admissible pair `x, y`, the axis substitution with
  parameter `x * y` is bijective.
* `lambdaMap_cop`: The coefficient extension intertwines the creation operators.
* `lambdaMap_copComp`: The coefficient extension intertwines the composite creation operators.
* `alphabetMap_gessel`: The coefficient extension fixes the fundamental quasisymmetric functions.
* `alphabetMap_realisation`: For realisations `ι` over `K` and `ι'` over `K'`,
  `alphabetMap φ (ι f) = ι' (lambdaMap φ f)`.
-/

@[expose] public section

namespace HJO.Ascent

open Finset HJO.Sym

section Transport

variable {K K' : Type*} [Field K] [Algebra ℚ K] [Field K'] [Algebra ℚ K']
variable (φ : K →ₐ[ℚ] K')

/-! ### Diagonal substitutions, the axis generators and the axis substitution -/

/-- A diagonal substitution transports, its scalar family going to the image family. -/
theorem lambdaMap_diagScale (c : ℕ → K) (f : Lambda K) :
    lambdaMap φ (diagScale c f) = diagScale (fun i => φ (c i)) (lambdaMap φ f) := by
  have h : ((lambdaMap φ).toRingHom.comp (diagScale c).toRingHom : Lambda K →+* Lambda K') =
      (diagScale fun i => φ (c i)).toRingHom.comp (lambdaMap φ).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · change lambdaMap φ (diagScale c (MvPolynomial.C a)) =
        diagScale (fun i => φ (c i)) (lambdaMap φ (MvPolynomial.C a))
      simp only [diagScale_C, lambdaMap_C]
    · change lambdaMap φ (diagScale c (MvPolynomial.X i)) =
        diagScale (fun i => φ (c i)) (lambdaMap φ (MvPolynomial.X i))
      simp only [diagScale_X, map_mul, lambdaMap_C, lambdaMap_X]
  exact RingHom.congr_fun h f

/-- **The coefficient extension commutes with the virtual axis alphabet.** The substitution
`f ↦ f[(1 - v)/v * X]` over `K` goes to the substitution `f ↦ f[(1 - φ v)/φ v * X]` over `K'`. -/
@[hjo "lem_asc_pleth_diff_qu"]
theorem lambdaMap_plethAxis (v : K) (f : Lambda K) :
    lambdaMap φ (plethAxis v f) = plethAxis (φ v) (lambdaMap φ f) := by
  rw [plethAxis_eq_diagScale, plethAxis_eq_diagScale, lambdaMap_diagScale]
  refine congrArg (fun c => diagScale c (lambdaMap φ f)) (funext fun i => ?_)
  rw [map_sub, map_inv₀, map_pow, map_one]

/-- **The coefficient extension fixes an axis generator.** The axis generator of degree `k` with
parameter `v` goes to the one with parameter `φ v`. -/
@[hjo "lem_asc_axis_gen"]
theorem lambdaMap_axisGen (v : K) (k : ℕ) :
    lambdaMap φ (axisGen v k) = axisGen (φ v) k := by
  rw [axisGen, axisGen, map_mul, lambdaMap_C, map_div₀, map_sub, map_one, lambdaMap_plethAxis,
    lambdaMap_completeHomog]

/-- The coefficient extension commutes with the axis substitution: extending coefficients after
substituting with parameter `v` is substituting the extension with parameter `φ v`. -/
theorem lambdaMap_axisSub (v : K) (f : Lambda K) :
    lambdaMap φ (axisSub v f) = axisSub (φ v) (lambdaMap φ f) := by
  have h : ((lambdaMap φ).toRingHom.comp (axisSub v).toRingHom : Lambda K →+* Lambda K') =
      (axisSub (φ v)).toRingHom.comp (lambdaMap φ).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · change lambdaMap φ (axisSub v (MvPolynomial.C a)) =
        axisSub (φ v) (lambdaMap φ (MvPolynomial.C a))
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, MvPolynomial.algebraMap_eq, lambdaMap_C,
        ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    · change lambdaMap φ (axisSub v (MvPolynomial.X i)) =
        axisSub (φ v) (lambdaMap φ (MvPolynomial.X i))
      rw [axisSub_X, lambdaMap_axisGen, lambdaMap_X, axisSub_X]
  exact RingHom.congr_fun h f

/-- A field carrying a `ℚ`-algebra structure has characteristic zero. -/
theorem charZero_of_algebra_rat (F : Type*) [Field F] [Algebra ℚ F] : CharZero F :=
  charZero_of_injective_algebraMap (algebraMap ℚ F).injective

/-- **The axis substitution is bijective at an admissible instance.** At an admissible pair
`x, y`, the axis generators with parameter `x * y` are a system of free generators of the
symmetric functions. -/
@[hjo "lem_asc_axis_free"]
theorem axisSub_bijective_of_isAdmissible {x y : K} (h : IsAdmissible x y) :
    Function.Bijective (axisSub (x * y)) :=
  haveI := charZero_of_algebra_rat K
  axisSub_bijective (mul_ne_zero h.fst_ne_zero h.snd_ne_zero) h.mul_pow_succ_ne_one

/-! ### The creation displacement and the creation operators -/

omit [Algebra ℚ K] in
/-- The creation displacement fixes the scalars, being an algebra map. -/
theorem plethCreate_C (q : K) (a : K) :
    plethCreate q (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Polynomial.algebraMap_apply,
    MvPolynomial.algebraMap_eq]

/-- **The coefficient extension commutes with the creation displacement.** Extending coefficients
after displacing with parameter `q` is displacing the extension with parameter `φ q`. -/
@[hjo "lem_asc_pleth_create"]
theorem laurentMap_plethCreate (q : K) (f : Lambda K) :
    laurentMap φ (plethCreate q f) = plethCreate (φ q) (lambdaMap φ f) := by
  have h : ((laurentMap φ).toRingHom.comp (plethCreate q).toRingHom :
      Lambda K →+* Polynomial (Lambda K')) =
      (plethCreate (φ q)).toRingHom.comp (lambdaMap φ).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · change laurentMap φ (plethCreate q (MvPolynomial.C a)) =
        plethCreate (φ q) (lambdaMap φ (MvPolynomial.C a))
      rw [plethCreate_C, laurentMap_C, lambdaMap_C, plethCreate_C]
    · change laurentMap φ (plethCreate q (MvPolynomial.X i)) =
        plethCreate (φ q) (lambdaMap φ (MvPolynomial.X i))
      rw [CreationSeeds.plethCreate_X, lambdaMap_X, CreationSeeds.plethCreate_X, map_sub, map_mul,
        map_pow, laurentMap_C, laurentMap_C, laurentMap_X, lambdaMap_powerSum, lambdaMap_C,
        map_sub, map_one, map_inv₀, map_pow]
  exact RingHom.congr_fun h f

/-- **The coefficient extension intertwines the creation operators.** For `q ∈ K` and `r : ℕ`,
`lambdaMap φ ∘ Cop q r = Cop (φ q) r ∘ lambdaMap φ`. -/
@[hjo "lem_asc_cop"]
theorem lambdaMap_cop (q : K) (r : ℕ) (f : Lambda K) :
    lambdaMap φ (Cop q r f) = Cop (φ q) r (lambdaMap φ f) := by
  change lambdaMap φ (coeffPairing (fun j => MvPolynomial.C ((-q) ^ (1 - (r : ℤ))) *
    completeHomog K (r + j)) (plethCreate q f)) = _
  rw [lambdaMap_coeffPairing, laurentMap_plethCreate]
  refine congrArg (fun c => coeffPairing c (plethCreate (φ q) (lambdaMap φ f)))
    (funext fun j => ?_)
  rw [map_mul, lambdaMap_C, map_zpow₀, map_neg, lambdaMap_completeHomog]

/-- The composite creation operator of a composition, read off its parts. -/
theorem copComp_cons (q : K) (r : ℕ) (α : List ℕ) :
    CopComp q (r :: α) = Cop q r * CopComp q α := by
  rw [CopComp, CopComp, List.map_cons, List.prod_cons]

/-- **The coefficient extension intertwines the composite creation operators.** For every
composition `α`, `lambdaMap φ ∘ CopComp q α = CopComp (φ q) α ∘ lambdaMap φ`. -/
@[hjo "lem_asc_cop_comp"]
theorem lambdaMap_copComp (q : K) (α : List ℕ) (f : Lambda K) :
    lambdaMap φ (CopComp q α f) = CopComp (φ q) α (lambdaMap φ f) := by
  induction α generalizing f with
  | nil => simp [CopComp]
  | cons r t ih =>
    rw [copComp_cons, copComp_cons, Module.End.mul_apply, Module.End.mul_apply, lambdaMap_cop, ih]

/-! ### The alphabet series -/

/-- **The coefficient extension of the alphabet series.** The map `K⟦x₁, x₂, …⟧ → K'⟦x₁, x₂, …⟧`
applying `φ` to every coefficient. -/
@[hjo "def_asc_alphabet_map"]
noncomputable def alphabetMap : AlphabetSeries K →ₐ[ℚ] AlphabetSeries K' :=
  MvPowerSeries.mapAlgHom φ

/-- The coefficient extension of the alphabet series is the coefficientwise map. -/
theorem alphabetMap_apply (F : AlphabetSeries K) :
    alphabetMap φ F = MvPowerSeries.map (φ : K →+* K') F := rfl

/-- Each coefficient of the coefficient extension of an alphabet series is the image under `φ` of
the corresponding coefficient. -/
@[simp]
theorem alphabetMap_coeff (F : AlphabetSeries K) (d : ℕ →₀ ℕ) :
    MvPowerSeries.coeff d (alphabetMap φ F) = φ (MvPowerSeries.coeff d F) := by
  rw [alphabetMap_apply, MvPowerSeries.coeff_map]
  rfl

/-- The structure map into the alphabet series is the constant series. -/
theorem algebraMap_alphabetSeries {F : Type*} [CommRing F] (a : F) :
    algebraMap F (AlphabetSeries F) a = MvPowerSeries.C a := by
  simp [MvPowerSeries.algebraMap_apply]

/-- The coefficient extension sends the constant series `a` to the constant series `φ a`. -/
@[simp]
theorem alphabetMap_C (a : K) :
    alphabetMap φ (MvPowerSeries.C a) = MvPowerSeries.C (φ a) := by
  rw [alphabetMap_apply, MvPowerSeries.map_C]
  rfl

/-- The image under a ring homomorphism of the indicator of a set, valued `1` on it, is the
indicator of the same set. -/
theorem map_indicator_one (s : Set (ℕ →₀ ℕ)) (d : ℕ →₀ ℕ) :
    φ (Set.indicator s (1 : (ℕ →₀ ℕ) → K) d) = Set.indicator s (1 : (ℕ →₀ ℕ) → K') d := by
  by_cases hd : d ∈ s
  · rw [Set.indicator_of_mem hd, Set.indicator_of_mem hd, Pi.one_apply, Pi.one_apply, map_one]
  · rw [Set.indicator_of_notMem hd, Set.indicator_of_notMem hd, map_zero]

/-- **The coefficient extension fixes a fundamental quasisymmetric function.** It sends `F_{n,S}`
over `K` to `F_{n,S}` over `K'`. -/
@[hjo "lem_asc_gessel"]
theorem alphabetMap_gessel (n : ℕ) (S : Finset ℕ) :
    alphabetMap φ (ParkingFunctions.gessel K n S) = ParkingFunctions.gessel K' n S := by
  refine MvPowerSeries.ext fun d => ?_
  rw [alphabetMap_coeff, MvPowerSeries.coeff_apply, MvPowerSeries.coeff_apply,
    ParkingFunctions.gessel, ParkingFunctions.gessel]
  exact map_indicator_one φ _ d

/-- **The coefficient extension is compatible with any two realisations.** For a realisation of
the symmetric functions over `K` and one over `K'`, extending the coefficients of the realised
series is the same as realising the extended symmetric function. -/
@[hjo "lem_asc_realisation"]
theorem alphabetMap_realisation {ι : Lambda K →ₐ[K] AlphabetSeries K}
    {ι' : Lambda K' →ₐ[K'] AlphabetSeries K'} (h : IsRealisation ι) (h' : IsRealisation ι')
    (f : Lambda K) : alphabetMap φ (ι f) = ι' (lambdaMap φ f) := by
  have hgen : ∀ i : ℕ, alphabetMap φ (ι (MvPolynomial.X i)) = ι' (MvPolynomial.X i) := by
    intro i
    refine MvPowerSeries.ext fun d => ?_
    rw [alphabetMap_coeff]
    have hpK : (MvPolynomial.X i : Lambda K) = powerSum K (i + 1) := by
      rw [powerSum, Nat.add_sub_cancel]
    have hpK' : (MvPolynomial.X i : Lambda K') = powerSum K' (i + 1) := by
      rw [powerSum, Nat.add_sub_cancel]
    by_cases hd : ∃ j : ℕ, d = Finsupp.single j (i + 1)
    · obtain ⟨j, rfl⟩ := hd
      rw [hpK, hpK', h.coeff_pow i j, h'.coeff_pow i j, map_one]
    · rw [hpK, hpK', h.coeff_of_ne i d fun j hj => hd ⟨j, hj⟩,
        h'.coeff_of_ne i d fun j hj => hd ⟨j, hj⟩, map_zero]
  have hcomp : ((alphabetMap φ).toRingHom.comp (ι : Lambda K →+* AlphabetSeries K) :
      Lambda K →+* AlphabetSeries K') =
      (ι' : Lambda K' →+* AlphabetSeries K').comp (lambdaMap φ).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · change alphabetMap φ (ι (MvPolynomial.C a)) = ι' (lambdaMap φ (MvPolynomial.C a))
      rw [lambdaMap_C, ← MvPolynomial.algebraMap_eq, ← MvPolynomial.algebraMap_eq,
        AlgHom.commutes, AlgHom.commutes, algebraMap_alphabetSeries, algebraMap_alphabetSeries,
        alphabetMap_C]
    · change alphabetMap φ (ι (MvPolynomial.X i)) = ι' (lambdaMap φ (MvPolynomial.X i))
      rw [lambdaMap_X, hgen]
  exact RingHom.congr_fun hcomp f

end Transport

end HJO.Ascent
