/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.HAlphabet
public import HJO.Collinear.Vocabulary
public meta import HJO.Attr

/-! # The two-variable plethystic displacement and its coefficients

The composite of one unstarred basic operator with one starred one is computed by displacing the
alphabet in two variables at once, `f[X + M/z₁ - M̃/z₂]`, and reading off the coefficient of
`z₁^{-s}z₂^{-r}`. Both displacements are written in the inverse variables, so the two-variable one
lands in an iterated polynomial ring rather than in a ring of Laurent polynomials, and it is
literally the coefficientwise application of one displacement to the other: `δ₂` is
`Polynomial.map δ` after `δ*`. That makes "do the starred displacement first" a case of
`Polynomial.coeff_map` rather than a lemma.

The two facts the commutator computation needs are the two ends of the diagonal specialisation
`z₁ ↦ q u z`, `z₂ ↦ z`. Under it the two displacements cancel -- `M/(q u z) = M̃/z` is exactly
`(1 - q^{-j})(1 - u^{-j}) = (q u)^{-j}(1 - q^j)(1 - u^j)` -- so the specialised two-variable
displacement of `f` is the constant `f`. Comparing coefficients of `z^{-n}` gives
`∑_{s} (q u)^{-s} f_{[s, n-s]} = 0` for every `n ≥ 1`. The constant coefficient `f_{[0,0]} = f` is
recorded separately and needs no hypothesis at all: extracting the coefficient of `w⁰` is a ring
homomorphism, and composed with either displacement it fixes every power sum, hence is the
identity.

The specialisation needs `q ≠ 0` and `u ≠ 0`, which come for free from working in
`ℚ(q, u)`: without them the starred displacement's scalars `1 - q^{-j}` are not the inverses the
cancellation is about.

Performing the two displacements in the other order gives the same coefficients. That is not
automatic here, since the two iterated polynomial rings differ in which variable is outermost, so
it is proved by exhibiting the exchange of the two variables as a ring homomorphism and checking
the two composites against it on the generators.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### Exchanging the two variables of an iterated polynomial ring -/

section Swap

variable {R : Type*} [CommRing R]

/-- Exchanging the two variables of `R[X][Y]`: the outer variable is sent to the inner one, and
each coefficient -- a polynomial in the inner variable -- is reread as a polynomial in the outer
one. -/
noncomputable def polySwap (R : Type*) [CommRing R] :
    Polynomial (Polynomial R) →+* Polynomial (Polynomial R) :=
  Polynomial.eval₂RingHom (Polynomial.mapRingHom (Polynomial.C : R →+* Polynomial R))
    (Polynomial.C Polynomial.X)

/-- The exchange rereads a constant of the outer variable as a polynomial in the inner one. -/
theorem polySwap_C (y : Polynomial R) :
    polySwap R (Polynomial.C y) = y.map Polynomial.C := by
  rw [polySwap, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.coe_mapRingHom]

/-- The exchange sends the outer variable to the inner one. -/
theorem polySwap_X :
    polySwap R (Polynomial.X : Polynomial (Polynomial R)) = Polynomial.C Polynomial.X := by
  rw [polySwap, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

/-- The exchange on a monomial of the outer variable. -/
theorem polySwap_monomial (n : ℕ) (b : Polynomial R) :
    polySwap R (Polynomial.monomial n b)
      = Polynomial.C (Polynomial.X ^ n) * b.map Polynomial.C := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, polySwap_C, polySwap_X,
    ← Polynomial.C_pow]
  ring

/-- **The exchange does exchange the two indices.** The coefficient of `Yʳ Xˢ` in the image is the
coefficient of `Yˢ Xʳ` in the argument. -/
theorem coeff_coeff_polySwap (P : Polynomial (Polynomial R)) (s r : ℕ) :
    ((polySwap R P).coeff r).coeff s = (P.coeff s).coeff r := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [map_add, Polynomial.coeff_add, Polynomial.coeff_add, hP, hQ, Polynomial.coeff_add,
      Polynomial.coeff_add]
  | monomial n b =>
    rw [polySwap_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_map, Polynomial.coeff_mul_C,
      Polynomial.coeff_X_pow, Polynomial.coeff_monomial]
    split_ifs with h1 h2 h2
    · rw [one_mul]
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rw [zero_mul, Polynomial.coeff_zero]

end Swap

/-! ### The displacement coefficients -/

section Coefficients

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The displacement coefficient `f_{[s]}`**, `HJO.Sym.shiftCoeff`: the coefficient
of `z^{-s}` in `f[X + M/z]`, which in the variable `w = z⁻¹` the displacement is written in is the
coefficient of `wˢ`. The `s ≥ 0` is the type `ℕ` of the index, with nothing
truncated. -/
@[hjo "def_shift_coeff"]
noncomputable def shiftCoeff (q u : L) (f : Lambda L) (s : ℕ) : Lambda L :=
  (plethShift q u f).coeff s

/-- **The starred displacement coefficient `f*_{[r]}`**, `HJO.Sym.shiftStarCoeff`: the
coefficient of `z^{-r}` in `f[X - M̃/z]`, again read as the coefficient of `wʳ` for `w = z⁻¹`. -/
@[hjo "def_shift_star_coeff"]
noncomputable def shiftStarCoeff (q u : L) (f : Lambda L) (r : ℕ) : Lambda L :=
  (plethShiftStar q u f).coeff r

omit [Algebra ℚ L] in
/-- The unstarred displacement fixes the scalars, being an algebra map. -/
theorem plethShift_C (q u : L) (a : L) :
    plethShift q u (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) := by
  simp [MvPolynomial.algebraMap_eq]

omit [Algebra ℚ L] in
/-- The starred displacement fixes the scalars, being an algebra map. -/
theorem plethShiftStar_C (q u : L) (a : L) :
    plethShiftStar q u (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) := by
  simp [MvPolynomial.algebraMap_eq]

omit [Algebra ℚ L] in
/-- The unstarred displacement on the generator of index `i`, which stands for `p_{i+1}`. -/
theorem plethShift_gen (q u : L) (i : ℕ) :
    plethShift q u (MvPolynomial.X i) = Polynomial.C (MvPolynomial.X i)
      + Polynomial.C (MvPolynomial.C ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1))))
        * Polynomial.X ^ (i + 1) := by
  rw [plethShift, MvPolynomial.aeval_X, CopPower.powerSum_succ]

omit [Algebra ℚ L] in
/-- The starred displacement on the generator of index `i`, which stands for `p_{i+1}`. -/
theorem plethShiftStar_gen (q u : L) (i : ℕ) :
    plethShiftStar q u (MvPolynomial.X i) = Polynomial.C (MvPolynomial.X i)
      - Polynomial.C (MvPolynomial.C ((1 - (q ^ (i + 1))⁻¹) * (1 - (u ^ (i + 1))⁻¹)))
        * Polynomial.X ^ (i + 1) := by
  rw [plethShiftStar_X, CopPower.powerSum_succ]

/-- The two-variable plethystic displacement `δ₂`, sending `f` to `f[X + M/z₁ - M̃/z₂]`: the
starred displacement followed by the unstarred one applied to each coefficient. Its outer variable
is `w₂ = z₂⁻¹` and its inner variable is `w₁ = z₁⁻¹`. -/
@[hjo "def_pleth_shift_pair"]
noncomputable def plethShiftPair (q u : L) :
    Lambda L →ₐ[L] Polynomial (Polynomial (Lambda L)) :=
  (Polynomial.mapAlgHom (plethShift q u)).comp (plethShiftStar q u)

/-- The same two-variable displacement built in the other order: the unstarred displacement
followed by the starred one applied to each coefficient. Its outer variable is `w₁` and its inner
variable is `w₂`. -/
noncomputable def plethShiftPairPlain (q u : L) :
    Lambda L →ₐ[L] Polynomial (Polynomial (Lambda L)) :=
  (Polynomial.mapAlgHom (plethShiftStar q u)).comp (plethShift q u)

/-- The two-variable displacement coefficient `f_{[s,r]}`: the coefficient of
`z₁^{-s} z₂^{-r}` in `f[X + M/z₁ - M̃/z₂]`. -/
@[hjo "def_shift_pair_coeff"]
noncomputable def shiftPairCoeff (q u : L) (f : Lambda L) (s r : ℕ) : Lambda L :=
  ((plethShiftPair q u f).coeff r).coeff s

omit [Algebra ℚ L] in
/-- **The starred displacement first.** The two-variable coefficient `f_{[s,r]}` is the unstarred
coefficient of the starred coefficient, `(f*_{[r]})_{[s]}` -- which is how `δ₂` is built. -/
theorem shiftPairCoeff_eq_shiftCoeff (q u : L) (f : Lambda L) (s r : ℕ) :
    shiftPairCoeff q u f s r = shiftCoeff q u (shiftStarCoeff q u f r) s := by
  rw [shiftPairCoeff, shiftCoeff, shiftStarCoeff, plethShiftPair, AlgHom.comp_apply,
    Polynomial.coe_mapAlgHom, Polynomial.coeff_map]
  rfl

omit [Algebra ℚ L] in
/-- The coefficient of the outer variable of the two-variable displacement is the unstarred
displacement of the starred coefficient. -/
theorem coeff_plethShiftPair (q u : L) (f : Lambda L) (r : ℕ) :
    (plethShiftPair q u f).coeff r = plethShift q u (shiftStarCoeff q u f r) := by
  rw [plethShiftPair, AlgHom.comp_apply, Polynomial.coe_mapAlgHom, Polynomial.coeff_map,
    shiftStarCoeff]
  rfl

omit [Algebra ℚ L] in
/-- **The two orders agree.** Exchanging the two variables carries the displacement performed in
the unstarred-first order to the one performed in the starred-first order: both are the
`ℚ`-algebra homomorphism sending `p_j` to
`p_j + (1-qʲ)(1-uʲ)w₁ʲ - (1-q^{-j})(1-u^{-j})w₂ʲ`, read with `w₂` outermost. -/
theorem polySwap_plethShiftPairPlain (q u : L) (f : Lambda L) :
    polySwap (Lambda L) (plethShiftPairPlain q u f) = plethShiftPair q u f := by
  have key : (polySwap (Lambda L)).comp
      (plethShiftPairPlain q u : Lambda L →+* Polynomial (Polynomial (Lambda L)))
      = (plethShiftPair q u : Lambda L →+* Polynomial (Polynomial (Lambda L))) := by
    refine MvPolynomial.ringHom_ext ?_ ?_
    · intro a
      simp only [RingHom.comp_apply, RingHom.coe_coe, plethShiftPairPlain, plethShiftPair,
        AlgHom.comp_apply, Polynomial.coe_mapAlgHom, plethShift_C, plethShiftStar_C,
        Polynomial.map_C, polySwap_C]
    · intro i
      simp only [RingHom.comp_apply, RingHom.coe_coe, plethShiftPairPlain, plethShiftPair,
        AlgHom.comp_apply, Polynomial.coe_mapAlgHom, plethShift_gen, plethShiftStar_gen,
        plethShift_C, plethShiftStar_C, Polynomial.map_C, Polynomial.map_X,
        map_add, map_sub, map_mul, map_pow, polySwap_C, polySwap_X]
      ring
  exact RingHom.congr_fun key f

omit [Algebra ℚ L] in
/-- **The unstarred displacement first.** The two-variable coefficient `f_{[s,r]}` is also the
starred coefficient of the unstarred coefficient, `(f_{[s]})*_{[r]}`. -/
theorem shiftPairCoeff_eq_shiftStarCoeff (q u : L) (f : Lambda L) (s r : ℕ) :
    shiftPairCoeff q u f s r = shiftStarCoeff q u (shiftCoeff q u f s) r := by
  rw [shiftPairCoeff, ← polySwap_plethShiftPairPlain, coeff_coeff_polySwap, shiftStarCoeff,
    shiftCoeff, plethShiftPairPlain, AlgHom.comp_apply, Polynomial.coe_mapAlgHom,
    Polynomial.coeff_map]
  rfl

omit [Algebra ℚ L] in
/-- **The two-variable displacement is a polynomial in the two inverse variables with the
displacement coefficients.** For every `f` there is a bound `N` beyond which every coefficient
`f_{[s,r]}` vanishes, and `f[X + M/z₁ - M̃/z₂]` is the corresponding finite double sum
`∑_{s,r} f_{[s,r]} z₁^{-s} z₂^{-r}`. -/
@[hjo "lem_shift_pair_expansion"]
theorem exists_bound_plethShiftPair (q u : L) (f : Lambda L) :
    ∃ N : ℕ, (∀ s r : ℕ, N ≤ s ∨ N ≤ r → shiftPairCoeff q u f s r = 0) ∧
      plethShiftPair q u f
        = ∑ r ∈ range N, ∑ s ∈ range N,
            Polynomial.monomial r (Polynomial.monomial s (shiftPairCoeff q u f s r)) := by
  classical
  set P := plethShiftPair q u f with hP
  -- a single bound dominating the degree in the outer variable and all the inner degrees
  obtain ⟨N, hNP, hNc⟩ : ∃ N : ℕ, P.natDegree < N ∧ ∀ r : ℕ, (P.coeff r).natDegree < N := by
    refine ⟨max (P.natDegree + 1)
      (((range (P.natDegree + 1)).sup fun r => (P.coeff r).natDegree) + 1), ?_, ?_⟩
    · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    · intro r
      rcases Nat.lt_or_ge P.natDegree r with hr | hr
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hr, Polynomial.natDegree_zero]
        exact lt_of_lt_of_le (Nat.succ_pos _) (le_max_left _ _)
      · have hle := Finset.le_sup (f := fun r => (P.coeff r).natDegree)
          (Finset.mem_range.2 (show r < P.natDegree + 1 by omega))
        exact lt_of_le_of_lt hle (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _))
  refine ⟨N, ?_, ?_⟩
  · intro s r hsr
    rw [shiftPairCoeff, ← hP]
    rcases hsr with hs | hr
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hNc r) hs)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hNP hr),
        Polynomial.coeff_zero]
  · rw [Polynomial.as_sum_range' P N hNP]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Polynomial.as_sum_range' (P.coeff r) N (hNc r), map_sum]
    exact Finset.sum_congr rfl fun s _ => by rw [shiftPairCoeff, ← hP]

/-! ### The constant coefficient -/

omit [Algebra ℚ L] in
/-- The constant displacement coefficient is the argument itself. Extracting the coefficient of
`w⁰` is a ring homomorphism, and composed with the displacement it fixes every power sum, hence is
the identity. -/
theorem shiftCoeff_zero (q u : L) (f : Lambda L) : shiftCoeff q u f 0 = f := by
  rw [shiftCoeff]
  induction f using MvPolynomial.induction_on with
  | C a => rw [plethShift_C, Polynomial.coeff_C_zero]
  | add p g hp hg => rw [map_add, Polynomial.coeff_add, hp, hg]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.mul_coeff_zero, hp, plethShift_gen, Polynomial.coeff_add,
      Polynomial.coeff_C_zero, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp

omit [Algebra ℚ L] in
/-- **The constant starred displacement coefficient** is likewise the
argument itself, `f*_{[0]} = f`. Extracting the coefficient of `w⁰` is a ring homomorphism, and
composed with the starred displacement it fixes every power sum, hence is the identity; no
condition on `q` or `u` is needed. -/
@[hjo "lem_ght_shift_star_const"]
theorem shiftStarCoeff_zero (q u : L) (f : Lambda L) : shiftStarCoeff q u f 0 = f := by
  rw [shiftStarCoeff]
  induction f using MvPolynomial.induction_on with
  | C a => rw [plethShiftStar_C, Polynomial.coeff_C_zero]
  | add p g hp hg => rw [map_add, Polynomial.coeff_add, hp, hg]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.mul_coeff_zero, hp, plethShiftStar_gen, Polynomial.coeff_sub,
      Polynomial.coeff_C_zero, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp

omit [Algebra ℚ L] in
/-- **The constant two-variable coefficient.** `f_{[0,0]} = f`, with no condition on the
parameters: each displacement separately fixes the coefficient of `w⁰`. -/
@[hjo "lem_shift_pair_const"]
theorem shiftPairCoeff_zero_zero (q u : L) (f : Lambda L) : shiftPairCoeff q u f 0 0 = f := by
  rw [shiftPairCoeff_eq_shiftCoeff, shiftStarCoeff_zero, shiftCoeff_zero]

/-! ### The diagonal specialisation -/

/-- Rescaling the inverse variable by `c`: the `Λ`-algebra endomorphism of `Λ[w]` sending `w` to
`c w`. It is the substitution `z ↦ c⁻¹ z` read in `w = z⁻¹`. -/
noncomputable def invScale (c : L) : Polynomial (Lambda L) →ₐ[Lambda L] Polynomial (Lambda L) :=
  Polynomial.aeval (Polynomial.C (MvPolynomial.C c) * Polynomial.X)

omit [Algebra ℚ L] in
/-- Rescaling fixes the elements not involving `w`. -/
@[simp]
theorem invScale_C (c : L) (b : Lambda L) :
    invScale c (Polynomial.C b) = Polynomial.C b := by
  rw [invScale, Polynomial.aeval_C]
  rfl

omit [Algebra ℚ L] in
/-- Rescaling multiplies `w` by `c`. -/
@[simp]
theorem invScale_X (c : L) :
    invScale c (Polynomial.X : Polynomial (Lambda L))
      = Polynomial.C (MvPolynomial.C c) * Polynomial.X := by
  rw [invScale, Polynomial.aeval_X]

omit [Algebra ℚ L] in
/-- Rescaling multiplies the coefficient of `wᵐ` by `cᵐ`. -/
theorem coeff_invScale (c : L) (y : Polynomial (Lambda L)) (m : ℕ) :
    (invScale c y).coeff m = MvPolynomial.C (c ^ m) * y.coeff m := by
  induction y using Polynomial.induction_on' with
  | add p g hp hg =>
    rw [map_add, Polynomial.coeff_add, hp, hg, Polynomial.coeff_add, mul_add]
  | monomial n b =>
    rw [invScale, Polynomial.aeval_monomial, mul_pow, ← Polynomial.C_pow, ← MvPolynomial.C_pow,
      show (algebraMap (Lambda L) (Polynomial (Lambda L))) b = Polynomial.C b from rfl,
      ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_monomial]
    split_ifs with h1 h2 h2
    · rw [h2, mul_one]
      ring
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rw [mul_zero, mul_zero]

/-- The diagonal specialisation `z₁ ↦ q u z`, `z₂ ↦ z`, read in the inverse variables: the outer
variable `w₂` goes to `w` and the inner variable `w₁` to `(q u)⁻¹ w`. -/
noncomputable def diagSpec (q u : L) :
    Polynomial (Polynomial (Lambda L)) →+* Polynomial (Lambda L) :=
  Polynomial.eval₂RingHom (invScale ((q * u)⁻¹) : Polynomial (Lambda L) →+* Polynomial (Lambda L))
    Polynomial.X

omit [Algebra ℚ L] in
/-- The specialisation on a constant of the outer variable. -/
@[simp]
theorem diagSpec_C (q u : L) (y : Polynomial (Lambda L)) :
    diagSpec q u (Polynomial.C y) = invScale ((q * u)⁻¹) y := by
  rw [diagSpec, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  rfl

omit [Algebra ℚ L] in
/-- The specialisation sends the outer variable to `w`. -/
@[simp]
theorem diagSpec_X (q u : L) :
    diagSpec q u (Polynomial.X : Polynomial (Polynomial (Lambda L))) = Polynomial.X := by
  rw [diagSpec, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

omit [Algebra ℚ L] in
/-- **The inverted parameter product on power sums.** `(1-q^{-j})(1-u^{-j})` equals
`(qu)^{-j}(1-q^j)(1-u^j)`; this is what makes the two displacements cancel on the diagonal, and it
is where `q ≠ 0` and `u ≠ 0` enter. -/
@[hjo "lem_Mtilde_power"]
theorem one_sub_inv_pow_mul (q u : L) (hq : q ≠ 0) (hu : u ≠ 0) (j : ℕ) :
    (1 - q ^ j) * (1 - u ^ j) * ((q * u)⁻¹) ^ j
      = (1 - (q ^ j)⁻¹) * (1 - (u ^ j)⁻¹) := by
  have hqj : q ^ j ≠ 0 := pow_ne_zero _ hq
  have huj : u ^ j ≠ 0 := pow_ne_zero _ hu
  rw [inv_pow, mul_pow]
  field_simp
  ring

omit [Algebra ℚ L] in
/-- **The coefficients of a specialised polynomial.** The coefficient of `wⁿ` in the
specialisation collects the coefficients of `w₁ˢ w₂^{n-s}` weighted by `(qu)^{-s}`. -/
theorem coeff_diagSpec (q u : L) (P : Polynomial (Polynomial (Lambda L))) (n : ℕ) :
    (diagSpec q u P).coeff n
      = ∑ s ∈ range (n + 1),
          MvPolynomial.C (((q * u) ^ s)⁻¹) * ((P.coeff (n - s)).coeff s) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [map_add, Polynomial.coeff_add, hP, hQ, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by
      rw [Polynomial.coeff_add, Polynomial.coeff_add, mul_add]
  | monomial r y =>
    rw [show diagSpec q u (Polynomial.monomial r y)
        = invScale ((q * u)⁻¹) y * Polynomial.X ^ r from by
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, diagSpec_C, diagSpec_X],
      Polynomial.coeff_mul_X_pow']
    split_ifs with hrn
    · rw [coeff_invScale,
        Finset.sum_eq_single_of_mem (n - r) (Finset.mem_range.2 (by omega)) ?_]
      · rw [Polynomial.coeff_monomial]
        split_ifs with hr
        · rw [inv_pow]
        · exact absurd (show r = n - (n - r) by omega) hr
      · intro t ht htne
        have htn : t ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
        rw [Polynomial.coeff_monomial]
        split_ifs with hr
        · exact absurd (show t = n - r by omega) htne
        · rw [Polynomial.coeff_zero, mul_zero]
    · refine (Finset.sum_eq_zero ?_).symm
      intro t ht
      have htn : t ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
      rw [Polynomial.coeff_monomial]
      split_ifs with hr
      · omega
      · rw [Polynomial.coeff_zero, mul_zero]

omit [Algebra ℚ L] in
/-- **The two displacements cancel on the diagonal.** Specialising `z₁` to `q u z` and `z₂` to `z`
turns `f[X + M/z₁ - M̃/z₂]` back into `f`, because the two displaced terms are then equal. -/
theorem diagSpec_plethShiftPair (q u : L) (hq : q ≠ 0) (hu : u ≠ 0) (f : Lambda L) :
    diagSpec q u (plethShiftPair q u f) = Polynomial.C f := by
  have key : (diagSpec q u).comp
      (plethShiftPair q u : Lambda L →+* Polynomial (Polynomial (Lambda L)))
      = (Polynomial.C : Lambda L →+* Polynomial (Lambda L)) := by
    refine MvPolynomial.ringHom_ext ?_ ?_
    · intro a
      simp only [RingHom.comp_apply, RingHom.coe_coe, plethShiftPair, AlgHom.comp_apply,
        Polynomial.coe_mapAlgHom, plethShiftStar_C, Polynomial.map_C, plethShift_C, diagSpec_C,
        invScale_C]
    · intro i
      -- the two displaced scalars agree on the diagonal
      have hs := one_sub_inv_pow_mul q u hq hu (i + 1)
      have hs' := congrArg (algebraMap L (Polynomial (Lambda L))) hs
      simp only [map_mul, map_sub, map_one, map_pow] at hs'
      have e : ∀ c : L, (Polynomial.C (MvPolynomial.C c) : Polynomial (Lambda L))
          = algebraMap L (Polynomial (Lambda L)) c := fun _ => rfl
      simp only [RingHom.comp_apply, RingHom.coe_coe, plethShiftPair, AlgHom.comp_apply,
        Polynomial.coe_mapAlgHom, plethShiftStar_gen, Polynomial.map_C, Polynomial.map_X,
        plethShift_gen, plethShift_C, map_sub, map_add, map_mul, map_pow, diagSpec_C,
        diagSpec_X, invScale_C, invScale_X]
      simp only [e, map_one]
      linear_combination (Polynomial.X ^ (i + 1) : Polynomial (Lambda L)) * hs'
  exact RingHom.congr_fun key f

omit [Algebra ℚ L] in
/-- **The higher two-variable coefficients cancel.** For every `n ≥ 1`,
`∑_{s=0}^{n} (q u)^{-s} f_{[s, n-s]} = 0`: the specialisation of the two-variable displacement is
the constant `f`, whose coefficient at `w ^ n` vanishes. -/
@[hjo "lem_shift_pair_alternating"]
theorem sum_inv_pow_mul_shiftPairCoeff (q u : L) (hq : q ≠ 0) (hu : u ≠ 0) (f : Lambda L)
    {n : ℕ} (hn : 1 ≤ n) :
    ∑ s ∈ range (n + 1),
        MvPolynomial.C (((q * u) ^ s)⁻¹) * shiftPairCoeff q u f s (n - s) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h : (diagSpec q u (plethShiftPair q u f)).coeff (m + 1)
      = (Polynomial.C f).coeff (m + 1) := by
    rw [diagSpec_plethShiftPair q u hq hu f]
  rw [coeff_diagSpec, Polynomial.coeff_C] at h
  simp only [shiftPairCoeff]
  simpa using h

end Coefficients

end HJO.Sym
