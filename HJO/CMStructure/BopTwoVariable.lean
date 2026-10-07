/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.LaurentSeries
public import HJO.CMStructure.LaurentZW
public import HJO.CarlssonMellit.Bop
public import HJO.CarlssonMellit.DoubleShift
public meta import HJO.Attr

/-! # The Hall--Littlewood operators in the second variable, and the two-variable series

The Haglund--Morse--Zabrocki block of the Carlsson--Mellit layer reads the family `B_r` twice: once
in the variable `z`, which is `HJO.Sym.Bop`, and once in a second variable `w`, and then compares
the two inside the two-variable ring `𝒵 = Λ[[z]][z⁻¹][[w]][w⁻¹]` of `HJO.Sym.LaurentZW`. This file
supplies the three objects that comparison needs: the inclusions of the Laurent *polynomials* into
the Laurent *series*, the coefficientwise displacement `β̂`, and the two-variable generating
function `Ψ_f`.

## Main definitions

* `HJO.Sym.ofLaurentPoly`: the inclusion `Λ[w, w⁻¹] → Λ[[w]][w⁻¹]`, and `HJO.Sym.laurentPolyLift`
  the same with the coefficients moved along a ring homomorphism.
* `HJO.Sym.mapLaurentSeries`: a ring homomorphism applied to every coefficient of a Laurent series.
* `HJO.Sym.polyToLaurentSeries`: the inclusion `Λ[w] → Λ[[z]][z⁻¹]` reading `w` as `z⁻¹`.
* `HJO.Sym.omegaSeries`, `HJO.Sym.omegaZ`, `HJO.Sym.omegaW`: the series `Ω` in one variable, and
  the two copies `Ω(z)` and `Ω(w)` of it inside `𝒵`.
* `HJO.Sym.bshiftCoeff`, the displacement `β` applied
  coefficientwise.
* `HJO.Sym.bpairSeries`, the series `Ψ_f`.
* `HJO.Sym.bpairCoeff`, the coefficient `φ_{a,b}(f)`.

## Main results

* `HJO.Sym.bop_eq_coeff_plethShiftW`.
* `HJO.Sym.bshiftCoeff` together with `HJO.Sym.bshiftCoeff_C_C`: that `β̂` is a `𝕜`-algebra
  homomorphism — a ring homomorphism by
  construction, and one fixing the base pointwise.

## Implementation notes

**Why the inclusions have to be built.** `Mathlib` identifies `R[[z]][z⁻¹]` with `LaurentSeries R`,
the Hahn series over `ℤ`, but has no map from `LaurentPolynomial R` into it, and the layer needs
one twice: the displacement `β'` of `HJO.Sym.plethShiftW` lands in `Λ[w, w⁻¹]` while the factor
`Ω(w)` it is multiplied by is a genuine power series, and the double displacement `β₂` of
`HJO.Sym.plethShiftTwo` lands in `Λ[z, z⁻¹][w, w⁻¹]` while `Ψ_f` lives in `𝒵`. Both are
`HJO.Sym.laurentPolyLift`, which is the universal property of `AddMonoidAlgebra` at the monomial
`w ↦ single 1 1`; the second is that lift taken with the first as its coefficient map, so no
separate two-variable construction is needed.

**`β` is read in `w = z⁻¹` and the inclusion inverts.** The `β` of
`HJO.Sym.plethHallLittlewood` has target `Polynomial (Lambda K)` in the variable `w = z⁻¹`, because
only non-negative powers of `z⁻¹` occur. `HJO.Sym.polyToLaurentSeries` therefore sends that
variable to `single (-1) 1`, the element `z⁻¹` of `Λ[[z]][z⁻¹]`, which is what makes
`HJO.Sym.ofLaurentPoly_plethShiftW` — the ring-homomorphism identity behind
`HJO.Sym.bop_eq_coeff_plethShiftW` — an identity and not merely a correspondence. The proof names an
isomorphism `ρ` carrying `z` to `w`; here the two displacements are compared directly inside the
single ring `Λ[[z]][z⁻¹]`, which is the same argument with the isomorphism absorbed into the two
targets.

**Coefficientwise maps stay `AddMonoidHom`-free.** `HJO.Sym.mapLaurentSeries` is a genuine ring
homomorphism, using `Mathlib`'s `HahnSeries.map_mul` and `HahnSeries.map_C`; the target of `β̂` is
`𝒵`, and the note on `HJO.Sym.bicoeff` records why no statement here mentions an `Algebra K 𝒵`
instance.

## References

The file supplies the definitions `HJO.Sym.bshiftCoeff` and `HJO.Sym.bpairSeries`, and the lemma
`HJO.Sym.bop_eq_coeff_plethShiftW`, used for the Haglund--Morse--Zabrocki relations.
-/

@[expose] public section

namespace HJO.Sym

/-! ### Laurent polynomials inside Laurent series -/

section Inclusions

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The monomials of `Λ[[z]][z⁻¹]`, as a monoid homomorphism from the exponent group: `n ↦ zⁿ`.
This is the datum the universal property of `AddMonoidAlgebra` is applied to. -/
noncomputable def singleMonoidHom (R : Type*) [CommRing R] :
    Multiplicative ℤ →* LaurentSeries R where
  toFun n := HahnSeries.single (Multiplicative.toAdd n) 1
  map_one' := HahnSeries.single_zero_one
  map_mul' a b := by
    rw [HahnSeries.single_mul_single, one_mul]
    rfl

/-- **The Laurent polynomials inside the Laurent series, with the coefficients moved along `φ`**:
the ring homomorphism from `R[w, w⁻¹]` to `S[[w]][w⁻¹]` sending `a wⁿ` to `φ(a) wⁿ`. -/
noncomputable def laurentPolyLift (φ : R →+* S) : LaurentPolynomial R →+* LaurentSeries S :=
  AddMonoidAlgebra.liftNCRingHom ((HahnSeries.C : S →+* LaurentSeries S).comp φ)
    (singleMonoidHom S) fun _ _ => Commute.all _ _

@[simp]
theorem laurentPolyLift_C (φ : R →+* S) (a : R) :
    laurentPolyLift φ (LaurentPolynomial.C a) = HahnSeries.C (φ a) := by
  rw [← LaurentPolynomial.single_eq_C, laurentPolyLift, AddMonoidAlgebra.liftNCRingHom_single,
    RingHom.comp_apply, singleMonoidHom]
  simp [HahnSeries.single_zero_one]

@[simp]
theorem laurentPolyLift_T (φ : R →+* S) (n : ℤ) :
    laurentPolyLift φ (LaurentPolynomial.T n) = HahnSeries.single n 1 := by
  rw [LaurentPolynomial.T, laurentPolyLift, AddMonoidAlgebra.liftNCRingHom_single,
    RingHom.comp_apply, map_one, HahnSeries.C_one, one_mul, singleMonoidHom]
  rfl

/-- **The Laurent polynomials inside the Laurent series**: the inclusion of `R[w, w⁻¹]` in
`R[[w]][w⁻¹]`. -/
noncomputable def ofLaurentPoly (R : Type*) [CommRing R] :
    LaurentPolynomial R →+* LaurentSeries R :=
  laurentPolyLift (RingHom.id R)

@[simp]
theorem ofLaurentPoly_C (a : R) : ofLaurentPoly R (LaurentPolynomial.C a) = HahnSeries.C a :=
  laurentPolyLift_C _ a

@[simp]
theorem ofLaurentPoly_T (n : ℤ) :
    ofLaurentPoly R (LaurentPolynomial.T n) = HahnSeries.single n 1 :=
  laurentPolyLift_T _ n

/-- **A ring homomorphism applied to every coefficient of a Laurent series.** -/
noncomputable def mapLaurentSeries (φ : R →+* S) : LaurentSeries R →+* LaurentSeries S where
  toFun x := x.map φ
  map_one' := by
    ext n
    rcases eq_or_ne n 0 with rfl | h
    · simp
    · simp [h]
  map_mul' x y := HahnSeries.map_mul (φ : R →ₙ+* S)
  map_zero' := by ext n; simp
  map_add' x y := by ext n; simp

@[simp]
theorem coeff_mapLaurentSeries (φ : R →+* S) (x : LaurentSeries R) (n : ℤ) :
    (mapLaurentSeries φ x).coeff n = φ (x.coeff n) := HahnSeries.map_coeff ..

/-- **The polynomials in `w = z⁻¹` inside the Laurent series in `z`**: the ring homomorphism
sending the variable to `z⁻¹`. This is where the displacement
`HJO.Sym.plethHallLittlewood`, whose target is the polynomial ring in `w = z⁻¹`, meets the
two-sided Laurent series in `z`. -/
noncomputable def polyToLaurentSeries (R : Type*) [CommRing R] :
    Polynomial R →+* LaurentSeries R :=
  Polynomial.eval₂RingHom (HahnSeries.C : R →+* LaurentSeries R) (HahnSeries.single (-1) 1)

@[simp]
theorem polyToLaurentSeries_C (a : R) :
    polyToLaurentSeries R (Polynomial.C a) = HahnSeries.C a := by
  rw [polyToLaurentSeries, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]

@[simp]
theorem polyToLaurentSeries_monomial (j : ℕ) (a : R) :
    polyToLaurentSeries R (Polynomial.monomial j a) = HahnSeries.single (-(j : ℤ)) a := by
  rw [polyToLaurentSeries, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
    HahnSeries.single_pow, HahnSeries.C_apply, HahnSeries.single_mul_single, one_pow, mul_one,
    zero_add, show (j • (-1 : ℤ)) = -(j : ℤ) by simp]

end Inclusions

/-! ### The alternating elementary series as a Laurent series -/

section Omega

variable (K : Type*) [CommRing K] [Algebra ℚ K]

/-- **The alternating elementary series as a Laurent series** `Ω(t) = ∑_{n ≥ 0}(-1)ⁿ eₙ tⁿ`, the
series `HJO.Sym.elemSymmSeries` read in `Λ[[t]][t⁻¹]`. -/
noncomputable def omegaSeries : LaurentSeries (Lambda K) :=
  HahnSeries.ofPowerSeries ℤ (Lambda K) (elemSymmSeries K)

variable {K}

/-- **The Laurent coefficients of `Ω`** are exactly the alternating elementary functions at an
integer index: `(-1)ⁿ eₙ` for `n ≥ 0` and `0` below. So the family `HJO.Sym.elemSymmAlt` against
which `HJO.Sym.Bop` pairs is the coefficient family of `Ω`, which is what makes the operators of
negative index right. -/
@[simp]
theorem coeff_omegaSeries (n : ℤ) : (omegaSeries K).coeff n = elemSymmAlt K n := by
  rcases lt_or_ge n 0 with hn | hn
  · rw [omegaSeries, HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_of_notMem_range,
      elemSymmAlt_of_neg hn]
    rintro ⟨m, hm⟩
    simp only [Nat.castOrderEmbedding_apply] at hm
    omega
  · lift n to ℕ using hn with m
    rw [omegaSeries, HahnSeries.ofPowerSeries_apply_coeff, coeff_elemSymmSeries,
      elemSymmAlt_natCast]

end Omega

/-! ### The Hall--Littlewood operators in the second variable -/

section BopW

variable {K : Type*} [CommRing K] [Algebra ℚ K]

omit [Algebra ℚ K] in
/-- **The two displacements are the same map into `Λ[[z]][z⁻¹]`.** The displacement `β'` of
`HJO.Sym.plethShiftW` and the displacement `β` of `HJO.Sym.plethHallLittlewood` send `p_k` to `p_k`
plus `(1-qᵏ)` times the inverse `k`-th power of their own variable, so including the first into the
Laurent series and reading the second's variable `w` as `z⁻¹` gives one ring homomorphism. This is
the isomorphism `ρ`, absorbed into the two targets. -/
theorem ofLaurentPoly_plethShiftW (q : K) (f : Lambda K) :
    ofLaurentPoly (Lambda K) (plethShiftW q f)
      = polyToLaurentSeries (Lambda K) (plethHallLittlewood q f) := by
  have h : (ofLaurentPoly (Lambda K)).comp
        (plethShiftW q : Lambda K →+* LaurentPolynomial (Lambda K))
      = (polyToLaurentSeries (Lambda K)).comp
        (plethHallLittlewood q : Lambda K →+* Polynomial (Lambda K)) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_coe, RingHom.coe_coe, plethShiftW_C,
        plethHallLittlewood_C, ofLaurentPoly_C, polyToLaurentSeries_C]
    · have hlhs : ofLaurentPoly (Lambda K)
            (LaurentPolynomial.C (powerSum K (i + 1)) +
              LaurentPolynomial.C (MvPolynomial.C (1 - q ^ (i + 1))) *
                LaurentPolynomial.T (-(i + 1 : ℤ)))
          = HahnSeries.single 0 (powerSum K (i + 1)) +
            HahnSeries.single (-((i : ℤ) + 1)) (MvPolynomial.C (1 - q ^ (i + 1))) := by
        rw [map_add, map_mul, ofLaurentPoly_C, ofLaurentPoly_C, ofLaurentPoly_T,
          HahnSeries.C_apply, HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
      have hrhs : polyToLaurentSeries (Lambda K)
            (Polynomial.C (powerSum K (i + 1)) +
              Polynomial.C (MvPolynomial.C (1 - q ^ (i + 1))) * Polynomial.X ^ (i + 1))
          = HahnSeries.single 0 (powerSum K (i + 1)) +
            HahnSeries.single (-((i : ℤ) + 1)) (MvPolynomial.C (1 - q ^ (i + 1))) := by
        rw [Polynomial.C_mul_X_pow_eq_monomial, map_add, polyToLaurentSeries_C,
          polyToLaurentSeries_monomial, HahnSeries.C_apply,
          show (-((i + 1 : ℕ) : ℤ)) = -((i : ℤ) + 1) by push_cast; ring]
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_coe, RingHom.coe_coe, plethShiftW_X,
        plethHallLittlewood_X, hlhs, hrhs]
  exact congrArg (fun g : Lambda K →+* LaurentSeries (Lambda K) => g f) h

/-- Pairing a polynomial in `w = z⁻¹` against the coefficients of `Ω` is the extraction of the
coefficient of `zʳ` from the product taken in `Λ[[z]][z⁻¹]`: the term `a wʲ` becomes the monomial
`a z^{-j}`, and `(a z^{-j} Ω)` has coefficient `a Ω_{r+j}` at `zʳ`. -/
theorem coeff_polyToLaurentSeries_mul_omegaSeries (r : ℤ) (P : Polynomial (Lambda K)) :
    (polyToLaurentSeries (Lambda K) P * omegaSeries K).coeff r
      = coeffPairing (fun j => elemSymmAlt K (r + j)) P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [map_add, add_mul, HahnSeries.coeff_add', Pi.add_apply, hP, hQ, map_add]
  | monomial j a =>
    rw [polyToLaurentSeries_monomial, HahnSeries.coeff_single_mul, coeff_omegaSeries,
      sub_neg_eq_add]
    change _ = Polynomial.sum _ (fun j A => A * elemSymmAlt K (r + j))
    rw [Polynomial.sum_monomial_index a (fun j A => A * elemSymmAlt K (r + j)) (by simp)]

/-- **The Hall--Littlewood operators in the second variable.** `HJO.Sym.bop_eq_coeff_plethShiftW`:
for every `r ∈ ℤ` and every `f ∈ Λ`, `B_r f = [wʳ](f[X - (q-1)/w] Ω(w))`, the product being taken in
`Λ[[w]][w⁻¹]`.

Here the second variable is named `z` — the two are interchangeable, and the point of the lemma is
that the operator does not depend on which letter the displacement uses. The displacement `β'` of
`HJO.Sym.plethShiftW`, whose target is the two-sided Laurent *polynomials*, is included into the
Laurent series by `HJO.Sym.ofLaurentPoly`, which is what lets it be multiplied by the genuine power
series `Ω`. -/
@[hjo "lem_cm_bop_w"]
theorem bop_eq_coeff_plethShiftW (q : K) (r : ℤ) (f : Lambda K) :
    Bop q r f
      = (ofLaurentPoly (Lambda K) (plethShiftW q f) * omegaSeries K).coeff r := by
  rw [ofLaurentPoly_plethShiftW, coeff_polyToLaurentSeries_mul_omegaSeries]
  rfl

end BopW

/-! ### The displacement applied coefficientwise, and the two-variable generating function -/

section Pair

variable {K : Type*} [CommRing K]

/-- **The displacement applied coefficientwise.** `HJO.Sym.bshiftCoeff`: the map
`β̂` from `Λ[[w]][w⁻¹]` to `𝒵` sending `∑_j c_j wʲ` to `∑_j β(c_j) wʲ`, the displacement `β` being
applied to each coefficient and its own variable `z` becoming the inner variable of `𝒵`.

It is built as a ring homomorphism, which is more than the definition asks for and is
what its first use needs.

**This is also half of the statement that `β̂` is a `𝕜`-algebra homomorphism.** Its type
carries the ring-homomorphism half — additive, unital and multiplicative, which is exactly what the
proof of that statement establishes — and
`HJO.Sym.bshiftCoeff_C_C` carries the other half, that the base is fixed pointwise. No
`Algebra K 𝒵` instance is named anywhere, for the reason recorded on `HJO.Sym.bicoeff`. -/
@[hjo "def_cm_bshift_coeff", hjo "lem_cm_bshift_coeff_hom"]
noncomputable def bshiftCoeff (q : K) : LaurentSeries (Lambda K) →+* LaurentZW K :=
  mapLaurentSeries ((polyToLaurentSeries (Lambda K)).comp (plethHallLittlewood q))

/-- **The defining property of `β̂`**: the coefficient of `wᵇ` of `β̂ G` is the displacement of the
coefficient of `wᵇ` of `G`, read in the inner variable `z` of `𝒵`. -/
@[hjo "def_cm_bshift_coeff"]
theorem coeff_bshiftCoeff (q : K) (G : LaurentSeries (Lambda K)) (b : ℤ) :
    (bshiftCoeff q G).coeff b
      = polyToLaurentSeries (Lambda K) (plethHallLittlewood q (G.coeff b)) := by
  rw [bshiftCoeff, coeff_mapLaurentSeries, RingHom.comp_apply, RingHom.coe_coe]

/-- **`HJO.Sym.bshiftCoeff`: `β̂` is a `𝕜`-algebra homomorphism.** The ring-homomorphism half is
the type of `HJO.Sym.bshiftCoeff`; this is the remaining half, that `β̂` fixes every scalar of the
base. A ring homomorphism fixing the image of `𝕜` pointwise *is* a `𝕜`-algebra homomorphism, and
multiplicativity together with a pointwise fixed base introduces no competing scalar action — which
is why the statement is made this way rather than as an `AlgHom`: `HahnSeries` carries both
`HahnSeries.instAlgebra` and `HahnSeries.powerSeriesAlgebra`, so on `𝒵` an `Algebra K 𝒵` instance is
a diamond and a statement naming one is a statement about whichever instance the elaborator reached
for. The scalar `c` of `𝕜` enters `Λ[[w]][w⁻¹]` and `𝒵` through the constant embeddings written out
below, where there is no ambiguity.

`β` is a `𝕜`-algebra homomorphism out of `Λ`, so it sends the constant `c` to the constant `c`; the
coefficientwise application therefore fixes the series that is `c` at `w⁰` and `0` elsewhere. -/
@[hjo "lem_cm_bshift_coeff_hom"]
theorem bshiftCoeff_C_C (q : K) (c : K) :
    bshiftCoeff q (HahnSeries.C (MvPolynomial.C c : Lambda K))
      = HahnSeries.C (HahnSeries.C (MvPolynomial.C c : Lambda K)) := by
  ext b
  rw [coeff_bshiftCoeff, HahnSeries.C_apply, HahnSeries.C_apply]
  rcases eq_or_ne b 0 with rfl | hb
  · rw [HahnSeries.coeff_single_same, HahnSeries.coeff_single_same, plethHallLittlewood_C,
      polyToLaurentSeries_C, HahnSeries.C_apply]
  · rw [HahnSeries.coeff_single_of_ne hb, HahnSeries.coeff_single_of_ne hb, map_zero, map_zero]

variable [Algebra ℚ K]

/-- **`Ω(z)` inside `𝒵`**: the series `Ω` in the inner variable, sitting at `w⁰`. -/
noncomputable def omegaZ (K : Type*) [CommRing K] [Algebra ℚ K] : LaurentZW K :=
  HahnSeries.C (omegaSeries K)

/-- **`Ω(w)` inside `𝒵`**: the series `Ω` in the outer variable, its coefficients sitting at
`z⁰`. -/
noncomputable def omegaW (K : Type*) [CommRing K] [Algebra ℚ K] : LaurentZW K :=
  mapLaurentSeries (HahnSeries.C : Lambda K →+* LaurentSeries (Lambda K)) (omegaSeries K)

/-- `Ω(z)` has the coefficient `(-1)^a e_a` at `z^a w^0` and nothing off `w⁰`. -/
theorem bicoeff_omegaZ (a b : ℤ) :
    bicoeff a b (omegaZ K) = if b = 0 then elemSymmAlt K a else 0 := by
  rw [bicoeff, omegaZ, HahnSeries.C_apply]
  split_ifs with h
  · rw [h, HahnSeries.coeff_single_same, coeff_omegaSeries]
  · rw [HahnSeries.coeff_single_of_ne h, HahnSeries.coeff_zero]

/-- `Ω(w)` has the coefficient `(-1)^b e_b` at `z^0 w^b` and nothing off `z⁰`. -/
theorem bicoeff_omegaW (a b : ℤ) :
    bicoeff a b (omegaW K) = if a = 0 then elemSymmAlt K b else 0 := by
  rw [bicoeff, omegaW, coeff_mapLaurentSeries, HahnSeries.C_apply]
  split_ifs with h
  · rw [h, HahnSeries.coeff_single_same, coeff_omegaSeries]
  · rw [HahnSeries.coeff_single_of_ne h]

/-- **The two-variable generating function.** `HJO.Sym.bpairSeries`:
`Ψ_f := β₂(f) Ω(z) Ω(w)`, an element of `𝒵`. The double displacement `β₂` of
`HJO.Sym.plethShiftTwo` lands in the Laurent polynomials in both variables, the subring of `𝒵` in
which its image lies, and is included by `HJO.Sym.laurentPolyLift` taken with
`HJO.Sym.ofLaurentPoly` as its coefficient map — the outer variable being `w` and the inner one
`z`, as in both `HJO.Sym.LaurentZW` and `HJO.Sym.plethShiftTwo`. -/
@[hjo "def_cm_bpair_series"]
noncomputable def bpairSeries (q : K) (f : Lambda K) : LaurentZW K :=
  laurentPolyLift (ofLaurentPoly (Lambda K)) (plethShiftTwo q f) * omegaZ K * omegaW K

/-- **The coefficients of the two-variable generating function.** This is
`HJO.Sym.bpairCoeff`: `φ_{a,b}(f) = [z^aw^b]Ψ_f`, an element of `Λ` for each pair of integers.

The extraction is `HJO.Sym.bicoeff`, which is additive and nothing more — see the note on
`HJO.Sym.bicoeff` for why no scalar action on `𝒵` is named. -/
@[hjo "def_cm_bpair_coeff"]
noncomputable def bpairCoeff (q : K) (a b : ℤ) (f : Lambda K) : Lambda K :=
  bicoeff a b (bpairSeries q f)

/-- **The defining property of `φ_{a,b}`**: it is the bivariate coefficient extraction applied to
`Ψ_f`. -/
@[hjo "def_cm_bpair_coeff"]
theorem bpairCoeff_apply (q : K) (a b : ℤ) (f : Lambda K) :
    bpairCoeff q a b f = bicoeff a b (bpairSeries q f) := rfl

/-- `Ψ_f` is additive in `f`: the double displacement is a ring homomorphism and the two factors
`Ω(z)`, `Ω(w)` are fixed. -/
theorem bpairSeries_add (q : K) (f g : Lambda K) :
    bpairSeries q (f + g) = bpairSeries q f + bpairSeries q g := by
  rw [bpairSeries, bpairSeries, bpairSeries, map_add, map_add, add_mul, add_mul]

/-- **`φ_{a,b}` is additive**, the extraction being additive and `Ψ` additive in `f`. -/
theorem bpairCoeff_add (q : K) (a b : ℤ) (f g : Lambda K) :
    bpairCoeff q a b (f + g) = bpairCoeff q a b f + bpairCoeff q a b g := by
  rw [bpairCoeff_apply, bpairCoeff_apply, bpairCoeff_apply, bpairSeries_add, bicoeff_add]

end Pair

end HJO.Sym
