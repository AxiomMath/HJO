/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.Algebra.Polynomial.Laurent
public import HJO.CMStructure.BopTwoVariable
public meta import HJO.Attr

/-! # The symmetry and the low-degree vanishing of the two-variable coefficients

The two-variable generating function `Ψ_f = β₂(f) Ω(z) Ω(w)` of `HJO.Sym.bpairSeries` has two
elementary properties that the Haglund--Morse--Zabrocki relations rest on: its coefficient family
`φ_{a,b}(f)` of `HJO.Sym.bpairCoeff` is symmetric in the pair `(a, b)`, and it vanishes once either
index drops low enough. This file proves both from one closed formula for the coefficients.

## Main results

* `HJO.Sym.bpairCoeff_comm`, that
  `φ_{a,b}(f) = φ_{b,a}(f)` for every `f ∈ Λ` and all `a, b ∈ ℤ`.
* `HJO.Sym.exists_bpairCoeff_eq_zero`, that for every
  `f ∈ Λ` there is an `N ≥ 0` with `φ_{a,b}(f) = 0` whenever `a < -N` or `b < -N`.

## Implementation notes

**Where the symmetry lives.** The textbook proof passes to the localisation of `Λ[[z,w]]` at `zw`
and uses the automorphism exchanging `z` and `w`. That automorphism does not exist on the ambient
`𝒵 = Λ[[z]][z⁻¹][[w]][w⁻¹]` of `HJO.Sym.LaurentZW`: an iterated Hahn series ring is genuinely
asymmetric in its two variables, since for each power of `w` the powers of `z` are bounded below by
a bound that may depend on that power of `w`. What *is* symmetric is the two-variable
Laurent *polynomial* ring `Λ[z, z⁻¹][w, w⁻¹]`, the target of the double displacement
`HJO.Sym.plethShiftTwo`, and that is where `HJO.Sym.swapLaurentTwo` is built — by the universal
property of `AddMonoidAlgebra` applied twice, exactly as `HJO.Sym.laurentPolyLift` is. The
localisation of the proof is replaced by the observation that the two `Ω` factors contribute the
manifestly symmetric weight `e_{a-i} e_{b-j}` to the bimonomial `z^i w^j`, which is the content of
`HJO.Sym.bicoeff_monomialZW_mul_omega`.

**Why both results come from one lemma.** `HJO.Sym.bicoeff_lift_bimonomial_mul_omega` evaluates the
bivariate coefficient of `Ψ` at a single bimonomial of `β₂(f)`, and
`HJO.Sym.induction_on_bimonomial` reduces any two-variable Laurent polynomial to a finite sum of
those. Symmetry is then the `(i, j) ↦ (j, i)` invariance of the weight together with the swap
invariance of `β₂` itself, and the vanishing is `HJO.Sym.elemSymmAlt_of_neg` applied to whichever of
`a - i`, `b - j` is negative. Neither argument needs the `Ω` factors to be multiplied out.

**The bound is an integer, as in the statement as usually written.**
`HJO.Sym.exists_bpairCoeff_eq_zero` produces `N : ℤ` together with `0 ≤ N`, rather than an `N : ℕ`,
because that is the shape the lemma using it, `HJO.Sym.bop_bop`, takes as a hypothesis. No truncated
subtraction occurs anywhere here: every index difference `a - i` is a difference of integers.

## References

This file proves `HJO.Sym.bpairCoeff_comm` and `HJO.Sym.exists_bpairCoeff_eq_zero`, two of the
ingredients of the Haglund--Morse--Zabrocki relations.
-/

@[expose] public section

namespace HJO.Sym

/-! ### Exchanging the two variables of a two-variable Laurent polynomial ring -/

section Swap

variable {R : Type*} [CommRing R]

/-- **The monomials of `R[T; T⁻¹]`**, as a monoid homomorphism from the exponent group: `n ↦ Tⁿ`.
This is the datum the universal property of `AddMonoidAlgebra` is applied to, the
Laurent-polynomial counterpart of `HJO.Sym.singleMonoidHom`. -/
noncomputable def tMonoidHom (R : Type*) [CommRing R] :
    Multiplicative ℤ →* LaurentPolynomial R where
  toFun n := LaurentPolynomial.T (Multiplicative.toAdd n)
  map_one' := LaurentPolynomial.T_zero
  map_mul' a b := by
    change LaurentPolynomial.T (Multiplicative.toAdd a + Multiplicative.toAdd b) = _
    rw [LaurentPolynomial.T_add]

@[simp]
theorem tMonoidHom_ofAdd (n : ℤ) :
    tMonoidHom R (Multiplicative.ofAdd n) = LaurentPolynomial.T n := rfl

/-- **The monomials of the inner variable, seen inside the two-variable Laurent polynomials**:
`n ↦ C (Tⁿ)`, that is `n ↦ zⁿ` read in `R[z, z⁻¹][w, w⁻¹]`. -/
noncomputable def ctMonoidHom (R : Type*) [CommRing R] :
    Multiplicative ℤ →* LaurentPolynomial (LaurentPolynomial R) where
  toFun n := LaurentPolynomial.C (LaurentPolynomial.T (Multiplicative.toAdd n))
  map_one' := by
    change LaurentPolynomial.C (LaurentPolynomial.T (0 : ℤ)) = 1
    rw [LaurentPolynomial.T_zero, map_one]
  map_mul' a b := by
    change LaurentPolynomial.C (LaurentPolynomial.T
      (Multiplicative.toAdd a + Multiplicative.toAdd b)) = _
    rw [LaurentPolynomial.T_add, map_mul]

@[simp]
theorem ctMonoidHom_ofAdd (n : ℤ) :
    ctMonoidHom R (Multiplicative.ofAdd n)
      = LaurentPolynomial.C (LaurentPolynomial.T n) := rfl

/-- **The inner variable read as the outer one**: the ring homomorphism from `R[z, z⁻¹]` to
`R[z, z⁻¹][w, w⁻¹]` sending `a zⁿ` to `a wⁿ`. It is the universal property of
`AddMonoidAlgebra` applied to the *outer* family of monomials. -/
noncomputable def innerToOuter (R : Type*) [CommRing R] :
    LaurentPolynomial R →+* LaurentPolynomial (LaurentPolynomial R) :=
  AddMonoidAlgebra.liftNCRingHom
    ((LaurentPolynomial.C : LaurentPolynomial R →+* LaurentPolynomial (LaurentPolynomial R)).comp
      (LaurentPolynomial.C : R →+* LaurentPolynomial R))
    (tMonoidHom (LaurentPolynomial R)) fun _ _ => Commute.all _ _

@[simp]
theorem innerToOuter_C (a : R) :
    innerToOuter R (LaurentPolynomial.C a)
      = LaurentPolynomial.C (LaurentPolynomial.C a) := by
  conv_lhs => rw [← LaurentPolynomial.single_eq_C]
  rw [innerToOuter, AddMonoidAlgebra.liftNCRingHom_single, RingHom.comp_apply, tMonoidHom_ofAdd,
    LaurentPolynomial.T_zero, mul_one]

@[simp]
theorem innerToOuter_T (n : ℤ) :
    innerToOuter R (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
  rw [LaurentPolynomial.T, innerToOuter, AddMonoidAlgebra.liftNCRingHom_single, map_one, one_mul,
    tMonoidHom_ofAdd]

/-- **The exchange of the two variables** of `R[z, z⁻¹][w, w⁻¹]`: the ring endomorphism fixing `R`
and carrying `z` to `w` and `w` to `z`. This is the automorphism `σ`, built where it
exists: on the two-variable Laurent *polynomials*, not on the iterated Laurent *series* ring
`HJO.Sym.LaurentZW`, which has no such automorphism. -/
noncomputable def swapLaurentTwo (R : Type*) [CommRing R] :
    LaurentPolynomial (LaurentPolynomial R) →+* LaurentPolynomial (LaurentPolynomial R) :=
  AddMonoidAlgebra.liftNCRingHom (innerToOuter R) (ctMonoidHom R) fun _ _ => Commute.all _ _

@[simp]
theorem swapLaurentTwo_C (c : LaurentPolynomial R) :
    swapLaurentTwo R (LaurentPolynomial.C c) = innerToOuter R c := by
  rw [← LaurentPolynomial.single_eq_C, swapLaurentTwo, AddMonoidAlgebra.liftNCRingHom_single,
    ctMonoidHom_ofAdd, LaurentPolynomial.T_zero, map_one, mul_one]

/-- The exchange carries the outer variable to the inner one: `w ↦ z`. -/
@[simp]
theorem swapLaurentTwo_T (n : ℤ) :
    swapLaurentTwo R (LaurentPolynomial.T n) = LaurentPolynomial.C (LaurentPolynomial.T n) := by
  rw [LaurentPolynomial.T, swapLaurentTwo, AddMonoidAlgebra.liftNCRingHom_single, map_one, one_mul,
    ctMonoidHom_ofAdd]

/-- The exchange fixes the base `R` pointwise. -/
@[simp]
theorem swapLaurentTwo_C_C (a : R) :
    swapLaurentTwo R (LaurentPolynomial.C (LaurentPolynomial.C a))
      = LaurentPolynomial.C (LaurentPolynomial.C a) := by
  rw [swapLaurentTwo_C, innerToOuter_C]

/-- The exchange carries the inner variable to the outer one: `z ↦ w`. -/
@[simp]
theorem swapLaurentTwo_C_T (n : ℤ) :
    swapLaurentTwo R (LaurentPolynomial.C (LaurentPolynomial.T n)) = LaurentPolynomial.T n := by
  rw [swapLaurentTwo_C, innerToOuter_T]

/-- **The exchange on a bimonomial** `a zⁱ wʲ`: it produces `a zʲ wⁱ`. -/
theorem swapLaurentTwo_bimonomial (a : R) (i j : ℤ) :
    swapLaurentTwo R (LaurentPolynomial.C (LaurentPolynomial.C a * LaurentPolynomial.T i) *
        LaurentPolynomial.T j)
      = LaurentPolynomial.C (LaurentPolynomial.C a * LaurentPolynomial.T j) *
        LaurentPolynomial.T i := by
  have h1 : LaurentPolynomial.C (LaurentPolynomial.C a * LaurentPolynomial.T i)
      = LaurentPolynomial.C (LaurentPolynomial.C a) *
        LaurentPolynomial.C (LaurentPolynomial.T i) := map_mul _ _ _
  have h2 : LaurentPolynomial.C (LaurentPolynomial.C a * LaurentPolynomial.T j)
      = LaurentPolynomial.C (LaurentPolynomial.C a) *
        LaurentPolynomial.C (LaurentPolynomial.T j) := map_mul _ _ _
  rw [h1, h2, map_mul, map_mul, swapLaurentTwo_C_C, swapLaurentTwo_C_T, swapLaurentTwo_T]
  ring

/-- **Induction over the two-variable Laurent polynomials by bimonomials**: a property closed under
addition and holding at every `a zⁱ wʲ` holds throughout `R[z, z⁻¹][w, w⁻¹]`. This is
`LaurentPolynomial.induction_on'` applied twice, once in each variable. -/
@[elab_as_elim]
theorem induction_on_bimonomial {motive : LaurentPolynomial (LaurentPolynomial R) → Prop}
    (P : LaurentPolynomial (LaurentPolynomial R))
    (add : ∀ p q, motive p → motive q → motive (p + q))
    (bimonomial : ∀ (i j : ℤ) (a : R),
      motive (LaurentPolynomial.C (LaurentPolynomial.C a * LaurentPolynomial.T i) *
        LaurentPolynomial.T j)) :
    motive P := by
  induction P using LaurentPolynomial.induction_on' with
  | add p q hp hq => exact add p q hp hq
  | C_mul_T j c =>
    induction c using LaurentPolynomial.induction_on' with
    | add c c' hc hc' =>
      rw [map_add, add_mul]
      exact add _ _ hc hc'
    | C_mul_T i a => exact bimonomial i j a

end Swap

/-! ### The bivariate coefficients of `Ψ` at a bimonomial -/

section Bimonomial

variable {K : Type*} [CommRing K] [Algebra ℚ K]

omit [Algebra ℚ K] in
/-- The inclusion of `Λ[z, z⁻¹][w, w⁻¹]` into `𝒵` carries the bimonomial `a zⁱ wʲ` to the monomial
`HJO.Sym.monomialZW` of the same bidegree. -/
theorem laurentPolyLift_bimonomial (a : Lambda K) (i j : ℤ) :
    laurentPolyLift (ofLaurentPoly (Lambda K))
        (LaurentPolynomial.C (LaurentPolynomial.C a * LaurentPolynomial.T i) *
          LaurentPolynomial.T j)
      = monomialZW i j a := by
  simp only [map_mul, laurentPolyLift_C, laurentPolyLift_T, ofLaurentPoly_C, ofLaurentPoly_T,
    HahnSeries.C_apply, HahnSeries.single_mul_single, monomialZW, zero_add, mul_one]

/-- **The weight the two `Ω` factors put on a monomial.** The coefficient of `z^a w^b` in
`c zⁱ wʲ Ω(z) Ω(w)` is `c e_{a-i} e_{b-j}`, where `e` is the alternating family
`HJO.Sym.elemSymmAlt`. The two variables enter through separate factors, so the weight is
manifestly invariant under exchanging `(a, i)` with `(b, j)`: this is the whole source of the
symmetry of `φ_{a,b}`. -/
theorem bicoeff_monomialZW_mul_omega (c : Lambda K) (i j a b : ℤ) :
    bicoeff a b (monomialZW i j c * omegaZ K * omegaW K)
      = c * elemSymmAlt K (a - i) * elemSymmAlt K (b - j) := by
  have hz : monomialZW i j c * omegaZ K
      = HahnSeries.single j (HahnSeries.single i c * omegaSeries K) := by
    rw [monomialZW, omegaZ, HahnSeries.C_apply, HahnSeries.single_mul_single, add_zero]
  rw [hz, bicoeff, HahnSeries.coeff_single_mul, omegaW, coeff_mapLaurentSeries, coeff_omegaSeries,
    HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero, HahnSeries.coeff_single_mul,
    coeff_omegaSeries]

/-- **The bivariate coefficient of `Ψ` at a single bimonomial of the double displacement.** This is
the closed formula both main results of this file are read off. -/
theorem bicoeff_lift_bimonomial_mul_omega (c : Lambda K) (i j a b : ℤ) :
    bicoeff a b (laurentPolyLift (ofLaurentPoly (Lambda K))
        (LaurentPolynomial.C (LaurentPolynomial.C c * LaurentPolynomial.T i) *
          LaurentPolynomial.T j) * omegaZ K * omegaW K)
      = c * elemSymmAlt K (a - i) * elemSymmAlt K (b - j) := by
  rw [laurentPolyLift_bimonomial, bicoeff_monomialZW_mul_omega]

/-- **Exchanging the two variables of a two-variable Laurent polynomial exchanges the two indices**
of the bivariate coefficient of its product with `Ω(z) Ω(w)`. This is the statement that
`σ` carries the coefficient of `z^a w^b` to the coefficient of `z^b w^a`, stated where `σ` exists:
the exchange acts on the polynomial factor, and the two `Ω` factors are exchanged by it because the
weight of `HJO.Sym.bicoeff_monomialZW_mul_omega` is symmetric. -/
theorem bicoeff_swapLaurentTwo (a b : ℤ)
    (P : LaurentPolynomial (LaurentPolynomial (Lambda K))) :
    bicoeff a b (laurentPolyLift (ofLaurentPoly (Lambda K)) (swapLaurentTwo (Lambda K) P)
        * omegaZ K * omegaW K)
      = bicoeff b a (laurentPolyLift (ofLaurentPoly (Lambda K)) P * omegaZ K * omegaW K) := by
  induction P using induction_on_bimonomial with
  | add p q hp hq =>
    simp only [map_add, add_mul, bicoeff_add]
    rw [hp, hq]
  | bimonomial i j c =>
    rw [swapLaurentTwo_bimonomial, bicoeff_lift_bimonomial_mul_omega,
      bicoeff_lift_bimonomial_mul_omega]
    ring

/-- **Every two-variable Laurent polynomial gives a `Ψ` with a bounded-below support.** A Laurent
polynomial is a finite sum of bimonomials, so some `N ≥ 0` bounds all the negative exponents
occurring in it; multiplying by `Ω(z) Ω(w)`, whose exponents are non-negative, can only raise
exponents, and the weight of `HJO.Sym.bicoeff_monomialZW_mul_omega` vanishes as soon as one of its
two index differences is negative. -/
theorem exists_forall_bicoeff_lift_mul_omega_eq_zero
    (P : LaurentPolynomial (LaurentPolynomial (Lambda K))) :
    ∃ N : ℤ, 0 ≤ N ∧ ∀ a b : ℤ, a < -N ∨ b < -N →
      bicoeff a b (laurentPolyLift (ofLaurentPoly (Lambda K)) P * omegaZ K * omegaW K) = 0 := by
  induction P using induction_on_bimonomial with
  | add p q hp hq =>
    obtain ⟨M, hM0, hM⟩ := hp
    obtain ⟨N, hN0, hN⟩ := hq
    refine ⟨max M N, le_max_of_le_left hM0, fun a b hab => ?_⟩
    have hMle : -max M N ≤ -M := neg_le_neg (le_max_left M N)
    have hNle : -max M N ≤ -N := neg_le_neg (le_max_right M N)
    have habM : a < -M ∨ b < -M := hab.imp (fun h => lt_of_lt_of_le h hMle)
      (fun h => lt_of_lt_of_le h hMle)
    have habN : a < -N ∨ b < -N := hab.imp (fun h => lt_of_lt_of_le h hNle)
      (fun h => lt_of_lt_of_le h hNle)
    simp only [map_add, add_mul, bicoeff_add]
    rw [hM a b habM, hN a b habN, add_zero]
  | bimonomial i j c =>
    obtain ⟨N, hN0, hNi, hNj⟩ : ∃ N : ℤ, 0 ≤ N ∧ -N ≤ i ∧ -N ≤ j :=
      ⟨max (max (-i) (-j)) 0, le_max_right _ _, by omega, by omega⟩
    refine ⟨N, hN0, fun a b hab => ?_⟩
    rw [bicoeff_lift_bimonomial_mul_omega]
    rcases hab with h | h
    · rw [elemSymmAlt_of_neg (show a - i < 0 by omega), mul_zero, zero_mul]
    · rw [elemSymmAlt_of_neg (show b - j < 0 by omega), mul_zero]

end Bimonomial

/-! ### The double displacement is symmetric in the two variables -/

section Shift

variable {K : Type*} [CommRing K]

/-- **The double displacement is unchanged by exchanging the two variables.** Both
`σ ∘ β₂` and `β₂` are ring homomorphisms out of `Λ` fixing the base and agreeing on each
generator, because `p_k + (1 - qᵏ)(z^{-k} + w^{-k})` is symmetric in `z` and `w`; so they agree
on all of `Λ`, which is the polynomial ring on the generators. -/
theorem swapLaurentTwo_plethShiftTwo (q : K) (f : Lambda K) :
    swapLaurentTwo (Lambda K) (plethShiftTwo q f) = plethShiftTwo q f := by
  have h : (swapLaurentTwo (Lambda K)).comp
        (plethShiftTwo q : Lambda K →+* LaurentPolynomial (LaurentPolynomial (Lambda K)))
      = (plethShiftTwo q : Lambda K →+* LaurentPolynomial (LaurentPolynomial (Lambda K))) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, RingHom.coe_coe, plethShiftTwo_C, swapLaurentTwo_C_C]
    · rw [RingHom.comp_apply, RingHom.coe_coe, plethShiftTwo_X, map_add, map_mul,
        swapLaurentTwo_C_C, swapLaurentTwo_C_C, map_add, swapLaurentTwo_C_T, swapLaurentTwo_T]
      ring
  exact congrArg (fun g : Lambda K →+* LaurentPolynomial (LaurentPolynomial (Lambda K)) => g f) h

end Shift

/-! ### The two main results -/

section Pair

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- `φ_{a,b}(f)` written out: the bivariate coefficient of the product of the included double
displacement with the two `Ω` factors. This is `HJO.Sym.bpairCoeff_apply` with
`HJO.Sym.bpairSeries` unfolded as well, the form both results below are proved in. -/
theorem bpairCoeff_eq_bicoeff (q : K) (a b : ℤ) (f : Lambda K) :
    bpairCoeff q a b f
      = bicoeff a b (laurentPolyLift (ofLaurentPoly (Lambda K)) (plethShiftTwo q f)
          * omegaZ K * omegaW K) := rfl

/-- **The two-variable coefficients are symmetric.** `HJO.Sym.bpairCoeff_comm`: for
every `f ∈ Λ` and all `a, b ∈ ℤ`, `φ_{a,b}(f) = φ_{b,a}(f)`.

The textbook proof argues inside the localisation of `Λ[[z,w]]` at `zw`, where the exchange `σ` of
the two variables is available. That localisation is not a subring of the ambient `𝒵` in any way
that carries an exchange — see the note at the head of this file — so the exchange is applied to the
polynomial factor `β₂(f)` alone, by `HJO.Sym.swapLaurentTwo_plethShiftTwo`, and the two `Ω` factors
are handled by `HJO.Sym.bicoeff_swapLaurentTwo`. -/
@[hjo "lem_cm_bpair_symmetric"]
theorem bpairCoeff_comm (q : K) (a b : ℤ) (f : Lambda K) :
    bpairCoeff q a b f = bpairCoeff q b a f := by
  rw [bpairCoeff_eq_bicoeff, bpairCoeff_eq_bicoeff]
  have h := bicoeff_swapLaurentTwo (K := K) a b (plethShiftTwo q f)
  rwa [swapLaurentTwo_plethShiftTwo] at h

/-- **The two-variable coefficients vanish in low degrees.** This is
`HJO.Sym.exists_bpairCoeff_eq_zero`: for every `f ∈ Λ` there is an integer `N ≥ 0` such that
`φ_{a,b}(f) = 0` whenever `a < -N` or `b < -N`.

The double displacement `β₂(f)` is a genuine two-variable Laurent polynomial, so finitely many
bimonomials occur in it and some `N ≥ 0` bounds all their negative exponents; the factors `Ω(z)`
and `Ω(w)` carry no negative exponent, so they cannot lower a bidegree. -/
@[hjo "lem_cm_bpair_support"]
theorem exists_bpairCoeff_eq_zero (q : K) (f : Lambda K) :
    ∃ N : ℤ, 0 ≤ N ∧ ∀ a b : ℤ, a < -N ∨ b < -N → bpairCoeff q a b f = 0 := by
  obtain ⟨N, hN0, hN⟩ := exists_forall_bicoeff_lift_mul_omega_eq_zero (plethShiftTwo q f)
  refine ⟨N, hN0, fun a b hab => ?_⟩
  rw [bpairCoeff_eq_bicoeff]
  exact hN a b hab

end Pair

end HJO.Sym
