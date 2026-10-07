/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.Localization.Integer
public import HJO.CarlssonMellit.SeriesGrading
public meta import HJO.Attr

/-! # The alphabet-graded subring of the Carlsson--Mellit series ring

The pieces `Z^{(k)}_d` of `HJO.CarlssonMellit.SeriesGrading` collect the series of `P°_k` whose
monomials all have total degree `d` in the merged alphabet `y_k, x₁, x₂, …`. This file assembles
them into the ring `Z^{(k)}` in which the lowering step of the Carlsson--Mellit analysis works,
proves the two facts that make the assembly a grading — the pieces multiply into one another's sum
of degrees, and they are independent — and defines the relabellings `ŝ_ρ` of the merged alphabet
that act on it.

Independence is where the arithmetic of the construction sits. A series in `Z^{(k)}_d` has
coefficient `c_α y_k^{\,d-|α|}` at the letter-monomial `x^α`, so two different degrees put two
different powers of `y_k` on the *same* letter-monomial, and what keeps them apart is that `y_k` is
transcendental over `𝕂(y₁, …, y_{k-1})`. That transcendence is the real content here, and it is also
what makes `ŝ_ρ` definable at all: the relabelling interchanges `y_k` with a letter, so it is not
induced by any substitution in `P°_k`, and the only way to say what it does is to read off the
coefficient `c_α` of each merged monomial, which is exactly the extraction that transcendence makes
unambiguous.

## Main definitions

* `HJO.Sym.zRing`: the alphabet-graded subring `Z^{(k+1)}`, the set of finite sums of members of the
  graded pieces.
* `HJO.Sym.yFracEval`, `HJO.Sym.yFracCoeff`: the evaluation `𝕂(y₁, …, y_k)[Y] → 𝕂(y₁, …, y_{k+1})`
  at `Y = y_{k+1}`, and the coefficient of `y_{k+1}^b` it inverts.
* `HJO.Sym.zMonomial`, `HJO.Sym.zCoeff`: the merged monomial `c z^ν` and the coefficient of `z^ν` in
  a series, for `ν` an exponent vector on the merged alphabet.
* `HJO.Sym.zPerm`: the relabelling `ŝ_ρ` of the merged alphabet along a permutation `ρ`.
* `HJO.Sym.auxSplitLast`: the splitting `𝕂[y₁, …, y_{k+1}] → 𝕂[y₁, …, y_k][Y]` of the last auxiliary
  variable, which is what proves the transcendence.
* `HJO.Sym.auxFracYPow`: the multiples of `y_{k+1}^b` by the lower coefficient field, as an additive
  subgroup, so that a finite sum of them is one again.

## Main results

* `HJO.Sym.eq_zero_of_sum_auxFracCastSucc_mul_yFrac_pow_eq_zero`: `y_{k+1}` is transcendental over
  `𝕂(y₁, …, y_k)`, in the form used here — a vanishing `𝕂(y₁, …, y_k)`-combination of powers
  of `y_{k+1}` has vanishing coefficients.
* `HJO.Sym.zGraded_mul_zGraded_subset`, `HJO.Sym.mul_mem_zGraded`: the alphabet grading is
  multiplicative, `Z^{(k+1)}_dZ^{(k+1)}_e ⊆ Z^{(k+1)}_{d+e}`.
* `HJO.Sym.eq_zero_of_sum_eq_zero_of_mem_zGraded`: the alphabet grading is direct.
* `HJO.Sym.zPerm_zMonomial`: `ŝ_ρ` carries the merged monomial `c z^ν` to `c z^{ρν}`, which is what
  the "carrying each monomial `∏_i z^{(k)}_{j_i}` to `∏_i z^{(k)}_{ρ(j_i)}`" says.
* `HJO.Sym.zPerm_add_of_mem_zRing`, `HJO.Sym.zPerm_auxFracCastSucc_smul_of_mem_zRing`: `ŝ_ρ` is
  `𝕂(y₁, …, y_k)`-linear on `Z^{(k+1)}`.
* `HJO.Sym.coeff_zPerm_of_mem_zGraded`, `HJO.Sym.coeff_zPerm_eq_zero_of_mem_zGraded`: the
  coefficients of `ŝ_ρ G` for `G` in a graded piece, in the two ranges that `HJO.Sym.zGraded`
  distinguishes.

## Implementation notes

*The level of the merged alphabet is `k + 1`*, as in `HJO.CarlssonMellit.SeriesGrading`:
the `Z^{(k)}` is defined for `k ≥ 1` with coefficients in `𝕂(y₁, …, y_{k-1})`, which at
the level `k + 1` is `HJO.Sym.AuxFrac K k` included by `HJO.Sym.auxFracCastSucc`, the distinguished
letter `y_k` of the merged alphabet being `HJO.Sym.yFrac K (Fin.last k)`. No subtraction appears on
the level, and — the convention of `HJO.Sym.zGraded`, which this file does not revisit — none on the
exponent either: a `y`-exponent is always a witness `b` to `b + |α| = d` and never `d - |α|`, which
would clip to `0` on the monomials the condition must exclude.

*`Z^{(k+1)}` is the set of finite sums, spelled out.* `HJO.Sym.pGradedAll` assembles the
free-variable grading as a supremum `⨆ d, pGraded K k d` of submodules, but `HJO.Sym.zGraded` is a
`Set` and not a `Submodule` — for the reason recorded in `HJO.CarlssonMellit.SeriesGrading`,
namely that the `Submodule` packaging would force a global `Algebra` instance between the fraction
fields of two polynomial rings — so there is no `⨆` to take, and the definition is spelled
out: a family `G_d ∈ Z^{(k+1)}_d`, zero outside a `Finset`, summed. What the supremum would
have given for free is proved instead: `HJO.Sym.zGraded_subset_zRing` and, for the independence,
`HJO.Sym.eq_zero_of_sum_eq_zero_of_mem_zGraded`.

*Transcendence is proved, not cited.* No Mathlib statement says `y_{k+1}` is transcendental over
the fraction field of `𝕂[y₁, …, y_k]` inside the fraction field of `𝕂[y₁, …, y_{k+1}]`, and the
statement wanted here is about a `Finset`-indexed combination rather than about a polynomial.
The proof clears denominators (`IsLocalization.exist_integer_multiples`, which is legitimate because
a common denominator is a non-zerodivisor and the fraction field is a field), so that the identity
becomes one between honest polynomials, and then splits off the last variable. The splitting is
`HJO.Sym.auxSplitLast`, `MvPolynomial.optionEquivLeft` after `MvPolynomial.rename` along
`finSuccEquiv' (Fin.last k)`; Mathlib's own `MvPolynomial.finSuccEquiv` is *not* it, since that
splits off the variable `0`, and the variable complementary to the renaming `Fin.castSucc` of
`HJO.Sym.auxFracCastSucc` is the last one.

*The merged alphabet is indexed by `Option ℕ`*, with `none` the distinguished letter `y_{k+1}` and
`some i` the letter `x_{i+1}` — so `HJO.Sym.zMonomial_single_none` and
`HJO.Sym.zMonomial_single_some` are the two value checks that pin the indexing, and the
letters `z^{(k+1)}_j` for `j ≥ k + 1` of `HJO.Sym.zvar` are these letters in this order. The choice
is made for its API: an exponent vector on the merged alphabet is a `ν : Option ℕ →₀ ℕ`, its two
parts are Mathlib's `Finsupp.some ν` and `ν none`, and `Finsupp.optionElim` assembles them, with
`Finsupp.some_optionElim` and `Finsupp.optionElim_some` for the round trips.
`HJO.Macdonald.SplitCoeff` reads a split alphabet the same way.

*`ŝ_ρ` is defined on all of `P°_{k+1}` and is the map on `Z^{(k+1)}`.* On a series whose
coefficient at some `x^α` is not polynomial in `y_{k+1}` over `𝕂(y₁, …, y_k)` the extraction
`HJO.Sym.yFracCoeff` returns `0`, so the value there is junk; every statement below accordingly
carries a membership hypothesis, and linearity is stated on `Z^{(k+1)}`, which is the ring it
concerns. A definition by cases on membership would be no more informative and would make
every rewrite carry a proof.

*`ρ` is an arbitrary permutation of the merged alphabet.* The usual restriction is to the `ρ`
fixing all but finitely many letters, and this is the right restriction for the *theorems*
about `ŝ_ρ` further on rather than for the definition — every permutation of the alphabet permutes
the monomials of a given degree. Nothing below needs the restriction, so nothing below carries it,
and the `ŝ_ρ` is this `HJO.Sym.zPerm` at a finitary `ρ`.

*The finiteness of the factorisations of a monomial* that the proof of
`HJO.Sym.zGraded_mul_zGraded_subset` invokes is `Finset.antidiagonal`, which is how
`MvPowerSeries.coeff_mul` states the coefficient of a product in the first place;
`HJO.CarlssonMellit.ZMonomialFactorisations` records that identification as
`HJO.Sym.finite_setOf_add_eq` and `HJO.Sym.coe_antidiagonal`, and the proof below sums over that
`Finset`.

*What this file does not prove.* That `Z^{(k+1)}` is a subring (`HJO.Sym.zSubring`),
that `ŝ_ρ` preserves each graded piece (`HJO.Sym.zPerm_image_zGraded_subset` — whose two clauses are
exactly `HJO.Sym.coeff_zPerm_of_mem_zGraded` and `HJO.Sym.coeff_zPerm_eq_zero_of_mem_zGraded`), and
that the relabellings compose and are automorphisms (`HJO.Sym.zPerm_zPerm`, `HJO.Sym.zPermEquiv`)
are separate
results.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 4. The grading and the relabellings are this library's apparatus rather than the
paper's, which works with divided differences over a field of rational functions. -/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K]

/-! ### Splitting off the last auxiliary variable -/

/-- The last auxiliary variable split off: the `𝕂`-algebra map
`𝕂[y₁, …, y_{k+1}] → 𝕂[y₁, …, y_k][Y]` carrying `y_{k+1}` to the polynomial variable `Y` and each
`y_l` with `l ≤ k` to itself. It is `MvPolynomial.finSuccEquiv` at the other end of the alphabet:
the variable split off is the last, because the renaming `Fin.castSucc` of `HJO.Sym.auxFracCastSucc`
is the one whose image misses it. -/
noncomputable def auxSplitLast (K : Type*) [CommRing K] (k : ℕ) :
    MvPolynomial (Fin (k + 1)) K →ₐ[K] Polynomial (MvPolynomial (Fin k) K) :=
  (MvPolynomial.optionEquivLeft K (Fin k)).toAlgHom.comp
    (MvPolynomial.rename (finSuccEquiv' (Fin.last k)))

/-- The splitting carries the last auxiliary variable to the polynomial variable. -/
@[simp]
theorem auxSplitLast_X_last (K : Type*) [CommRing K] (k : ℕ) :
    auxSplitLast K k (MvPolynomial.X (Fin.last k)) = Polynomial.X := by
  simp [auxSplitLast]

/-- The splitting carries a polynomial in the first `k` auxiliary variables to a constant: those
variables are the coefficients of the polynomial ring it lands in. -/
@[simp]
theorem auxSplitLast_rename_castSucc {k : ℕ} (p : MvPolynomial (Fin k) K) :
    auxSplitLast K k (MvPolynomial.rename Fin.castSucc p) = Polynomial.C p := by
  have h : ((auxSplitLast K k).toRingHom.comp
      (MvPolynomial.rename (Fin.castSucc : Fin k → Fin (k + 1))).toRingHom) =
      (Polynomial.C : MvPolynomial (Fin k) K →+* Polynomial (MvPolynomial (Fin k) K)) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp [auxSplitLast]
    · have h1 : finSuccEquiv' (Fin.last k) (Fin.castSucc i) = some i := by
        rw [← Fin.succAbove_last]
        exact finSuccEquiv'_succAbove _ _
      simp [auxSplitLast, Function.comp_def, h1]
  exact RingHom.congr_fun h p

/-! ### The last auxiliary variable is transcendental over the lower coefficient field -/

/-- **`y_{k+1}` is transcendental over `𝕂(y₁, …, y_k)`**, in the form the alphabet grading uses it:
a finite `𝕂(y₁, …, y_k)`-combination `∑_b c_b y_{k+1}^b` that vanishes in `𝕂(y₁, …, y_{k+1})` has
every `c_b = 0`. Clearing the denominators of the finitely many `c_b` turns the hypothesis into an
identity between polynomials, in which `HJO.Sym.auxSplitLast` reads off the coefficient of each
power of `y_{k+1}` separately. -/
theorem eq_zero_of_sum_auxFracCastSucc_mul_yFrac_pow_eq_zero [IsDomain K] {k : ℕ} {s : Finset ℕ}
    {c : ℕ → AuxFrac K k}
    (h : ∑ b ∈ s, auxFracCastSucc K k (c b) * yFrac K (Fin.last k) ^ b = 0) {b : ℕ}
    (hb : b ∈ s) : c b = 0 := by
  classical
  have hy : yFrac K (Fin.last k)
      = algebraMap (MvPolynomial (Fin (k + 1)) K) (AuxFrac K (k + 1))
          (MvPolynomial.X (Fin.last k)) := rfl
  obtain ⟨a, ha⟩ :=
    IsLocalization.exist_integer_multiples (nonZeroDivisors (MvPolynomial (Fin k) K)) s c
  simp only [IsLocalization.IsInteger] at ha
  choose! p hp using ha
  have hpoly : ∑ b' ∈ s, MvPolynomial.rename Fin.castSucc (p b')
      * MvPolynomial.X (Fin.last k) ^ b' = 0 := by
    refine IsFractionRing.injective (MvPolynomial (Fin (k + 1)) K) (AuxFrac K (k + 1)) ?_
    rw [map_sum, map_zero]
    calc ∑ b' ∈ s, algebraMap (MvPolynomial (Fin (k + 1)) K) (AuxFrac K (k + 1))
            (MvPolynomial.rename Fin.castSucc (p b') * MvPolynomial.X (Fin.last k) ^ b')
        = auxFracCastSucc K k (algebraMap (MvPolynomial (Fin k) K) (AuxFrac K k) a)
            * ∑ b' ∈ s, auxFracCastSucc K k (c b') * yFrac K (Fin.last k) ^ b' := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b' hb' => ?_
          rw [map_mul, map_pow, ← auxFracCastSucc_algebraMap, hp b' hb', Algebra.smul_def,
            map_mul, hy]
          ring
      _ = 0 := by rw [h, mul_zero]
  have hp0 : p b = 0 := by
    have h1 := congrArg (auxSplitLast K k) hpoly
    rw [map_sum, map_zero] at h1
    simp only [map_mul, map_pow, auxSplitLast_rename_castSucc, auxSplitLast_X_last] at h1
    have h2 := congrArg (fun q : Polynomial (MvPolynomial (Fin k) K) => q.coeff b) h1
    simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow, hb] using h2
  have ha0 : algebraMap (MvPolynomial (Fin k) K) (AuxFrac K k) (a : MvPolynomial (Fin k) K)
      ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
    exact nonZeroDivisors.coe_ne_zero a
  have h3 := hp b hb
  rw [hp0, map_zero, Algebra.smul_def] at h3
  exact (mul_eq_zero.1 h3.symm).resolve_left ha0

/-! ### The polynomials in the last auxiliary variable -/

/-- Evaluation of a polynomial over `𝕂(y₁, …, y_k)` at the last auxiliary variable `y_{k+1}`: the
`𝕂(y₁, …, y_k)`-combinations of powers of `y_{k+1}`, which is where every coefficient of a member of
`Z^{(k+1)}_d` lives. -/
noncomputable def yFracEval (K : Type*) [CommRing K] [IsDomain K] (k : ℕ) :
    Polynomial (AuxFrac K k) →+* AuxFrac K (k + 1) :=
  Polynomial.eval₂RingHom (auxFracCastSucc K k) (yFrac K (Fin.last k))

/-- The evaluation, written out as the sum over the support. -/
theorem yFracEval_apply [IsDomain K] {k : ℕ} (p : Polynomial (AuxFrac K k)) :
    yFracEval K k p
      = ∑ b ∈ p.support, auxFracCastSucc K k (p.coeff b) * yFrac K (Fin.last k) ^ b := by
  rw [yFracEval, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum, Polynomial.sum_def]

/-- On a constant the evaluation is the inclusion of the lower coefficient field. -/
@[simp]
theorem yFracEval_C [IsDomain K] {k : ℕ} (c : AuxFrac K k) :
    yFracEval K k (Polynomial.C c) = auxFracCastSucc K k c := by
  simp [yFracEval]

/-- On a monomial the evaluation is the scalar multiple of a power of `y_{k+1}` that is
written `c_α y_k^{\,d-|α|}`. -/
@[simp]
theorem yFracEval_C_mul_X_pow [IsDomain K] {k : ℕ} (c : AuxFrac K k) (b : ℕ) :
    yFracEval K k (Polynomial.C c * Polynomial.X ^ b)
      = auxFracCastSucc K k c * yFrac K (Fin.last k) ^ b := by
  simp [yFracEval]

/-- The evaluation is injective: this is the transcendence of `y_{k+1}`,
`HJO.Sym.eq_zero_of_sum_auxFracCastSucc_mul_yFrac_pow_eq_zero`, packaged as the uniqueness of the
polynomial a `𝕂(y₁, …, y_k)`-combination of powers of `y_{k+1}` comes from. -/
theorem yFracEval_injective (K : Type*) [CommRing K] [IsDomain K] (k : ℕ) :
    Function.Injective (yFracEval K k) := by
  refine (injective_iff_map_eq_zero _).2 fun p hp => Polynomial.ext fun b => ?_
  rw [Polynomial.coeff_zero]
  by_cases hb : b ∈ p.support
  · exact eq_zero_of_sum_auxFracCastSucc_mul_yFrac_pow_eq_zero
      ((yFracEval_apply p).symm.trans hp) hb
  · exact Polynomial.notMem_support_iff.1 hb

/-- The coefficient of `y_{k+1}^b` in an element of `𝕂(y₁, …, y_{k+1})`: the `b`-th coefficient of
the polynomial over `𝕂(y₁, …, y_k)` evaluating to it at `y_{k+1}`, and `0` for an element that is
not such a polynomial. The polynomial is unique by `HJO.Sym.yFracEval_injective`, so the value is
the coefficient read off when an element of `Z^{(k+1)}_d` is written as
`∑_α c_α y_{k+1}^{\,d-|α|}x^α`. -/
noncomputable def yFracCoeff (K : Type*) [CommRing K] [IsDomain K] (k : ℕ)
    (x : AuxFrac K (k + 1)) (b : ℕ) : AuxFrac K k :=
  (Function.invFun (yFracEval K k) x).coeff b

/-- The extraction inverts the evaluation. -/
@[simp]
theorem yFracCoeff_yFracEval [IsDomain K] {k : ℕ} (p : Polynomial (AuxFrac K k)) (b : ℕ) :
    yFracCoeff K k (yFracEval K k p) b = p.coeff b := by
  rw [yFracCoeff, Function.leftInverse_invFun (yFracEval_injective K k) p]

/-- Every coefficient of `0` is `0`. -/
@[simp]
theorem yFracCoeff_zero [IsDomain K] {k b : ℕ} : yFracCoeff K k 0 b = 0 := by
  have h := yFracCoeff_yFracEval (0 : Polynomial (AuxFrac K k)) b
  rwa [map_zero, Polynomial.coeff_zero] at h

/-- The coefficients of a single scaled power of `y_{k+1}`. -/
theorem yFracCoeff_mul_yFrac_pow [IsDomain K] {k : ℕ} (c : AuxFrac K k) (b b' : ℕ) :
    yFracCoeff K k (auxFracCastSucc K k c * yFrac K (Fin.last k) ^ b) b'
      = if b' = b then c else 0 := by
  rw [← yFracEval_C_mul_X_pow, yFracCoeff_yFracEval]
  simp [Polynomial.coeff_X_pow]

/-- The extraction is additive where it is meaningful, that is on the polynomials in `y_{k+1}`. -/
theorem yFracCoeff_add_of_mem_range [IsDomain K] {k : ℕ} {x y : AuxFrac K (k + 1)}
    (hx : x ∈ (yFracEval K k).range) (hy : y ∈ (yFracEval K k).range) (b : ℕ) :
    yFracCoeff K k (x + y) b = yFracCoeff K k x b + yFracCoeff K k y b := by
  obtain ⟨p, rfl⟩ := RingHom.mem_range.1 hx
  obtain ⟨q, rfl⟩ := RingHom.mem_range.1 hy
  rw [← map_add, yFracCoeff_yFracEval, yFracCoeff_yFracEval, yFracCoeff_yFracEval,
    Polynomial.coeff_add]

/-- The extraction commutes with a finite sum of polynomials in `y_{k+1}`. -/
theorem yFracCoeff_sum_of_mem_range [IsDomain K] {k : ℕ} {ι : Type*} {t : Finset ι}
    {x : ι → AuxFrac K (k + 1)} (hx : ∀ i ∈ t, x i ∈ (yFracEval K k).range) (b : ℕ) :
    yFracCoeff K k (∑ i ∈ t, x i) b = ∑ i ∈ t, yFracCoeff K k (x i) b := by
  classical
  choose! p hp using fun i (hi : i ∈ t) => RingHom.mem_range.1 (hx i hi)
  have hsum : ∑ i ∈ t, x i = yFracEval K k (∑ i ∈ t, p i) :=
    (map_sum (yFracEval K k) p t).symm ▸ Finset.sum_congr rfl fun i hi => (hp i hi).symm
  rw [hsum, yFracCoeff_yFracEval, Polynomial.finsetSum_coeff]
  exact Finset.sum_congr rfl fun i hi => by rw [← hp i hi, yFracCoeff_yFracEval]

/-- The extraction is homogeneous for the scalars of the lower coefficient field. -/
theorem yFracCoeff_auxFracCastSucc_mul [IsDomain K] {k : ℕ} {x : AuxFrac K (k + 1)}
    (hx : x ∈ (yFracEval K k).range) (a : AuxFrac K k) (b : ℕ) :
    yFracCoeff K k (auxFracCastSucc K k a * x) b = a * yFracCoeff K k x b := by
  obtain ⟨p, rfl⟩ := RingHom.mem_range.1 hx
  rw [← yFracEval_C a, ← map_mul, yFracCoeff_yFracEval, yFracCoeff_yFracEval,
    Polynomial.coeff_C_mul]

/-! ### The multiples of a power of the last auxiliary variable -/

/-- The additive subgroup `𝕂(y₁, …, y_k)y_{k+1}^b` of the coefficient field of `P°_{k+1}`: the
elements written `c_α y_k^{\,d-|α|}`, packaged so that a finite sum of them is one
again. -/
noncomputable def auxFracYPow (K : Type*) [CommRing K] [IsDomain K] (k b : ℕ) :
    AddSubgroup (AuxFrac K (k + 1)) :=
  AddMonoidHom.range ((AddMonoidHom.mulRight (yFrac K (Fin.last k) ^ b)).comp
    (auxFracCastSucc K k).toAddMonoidHom)

/-- Membership in `𝕂(y₁, …, y_k)y_{k+1}^b`, unfolded. -/
theorem mem_auxFracYPow [IsDomain K] {k b : ℕ} {x : AuxFrac K (k + 1)} :
    x ∈ auxFracYPow K k b ↔
      ∃ c : AuxFrac K k, x = auxFracCastSucc K k c * yFrac K (Fin.last k) ^ b := by
  simp [auxFracYPow, eq_comm]

variable [IsDomain K] {k d e : ℕ} {G H : AuxAlphabetSeriesFrac K (k + 1)}

/-! ### The alphabet grading is multiplicative -/

/-- **The alphabet grading is multiplicative**, elementwise: the product of a series of merged
degree `d` and one of merged degree `e` has merged degree `d + e`. The coefficient of a
letter-monomial in the product is the finite sum over its factorisations, and a pair of factors
contributes only when the `y`-exponents and the letter-degrees add up to `d` and to `e`
respectively, in which case the contribution is a multiple of the single power `y_{k+1}^b` with
`b + |α| = d + e`. -/
theorem mul_mem_zGraded (hG : G ∈ zGraded K k d) (hH : H ∈ zGraded K k e) :
    G * H ∈ zGraded K k (d + e) := by
  classical
  refine ⟨fun α b hb => ?_, fun α hα => ?_⟩
  · rw [← mem_auxFracYPow, MvPowerSeries.coeff_mul]
    refine sum_mem fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    have hdeg : Finsupp.degree p.1 + Finsupp.degree p.2 = Finsupp.degree α := by
      rw [← hp, map_add]
    rcases lt_or_ge d (Finsupp.degree p.1) with h1 | h1
    · rw [coeff_eq_zero_of_mem_zGraded hG h1, zero_mul]
      exact zero_mem _
    rcases lt_or_ge e (Finsupp.degree p.2) with h2 | h2
    · rw [coeff_eq_zero_of_mem_zGraded hH h2, mul_zero]
      exact zero_mem _
    obtain ⟨c, hc⟩ :=
      exists_coeff_eq_of_mem_zGraded hG p.1 (b := d - Finsupp.degree p.1) (by omega)
    obtain ⟨c', hc'⟩ :=
      exists_coeff_eq_of_mem_zGraded hH p.2 (b := e - Finsupp.degree p.2) (by omega)
    refine mem_auxFracYPow.2 ⟨c * c', ?_⟩
    rw [hc, hc', map_mul,
      show b = d - Finsupp.degree p.1 + (e - Finsupp.degree p.2) by omega, pow_add]
    ring
  · rw [MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    have hdeg : Finsupp.degree p.1 + Finsupp.degree p.2 = Finsupp.degree α := by
      rw [← hp, map_add]
    rcases lt_or_ge d (Finsupp.degree p.1) with h1 | h1
    · rw [coeff_eq_zero_of_mem_zGraded hG h1, zero_mul]
    · rw [coeff_eq_zero_of_mem_zGraded hH (by omega), mul_zero]

open scoped Pointwise in
/-- **The alphabet grading is multiplicative**: `Z^{(k+1)}_dZ^{(k+1)}_e ⊆ Z^{(k+1)}_{d+e}`, the
product of the two sets being taken elementwise. -/
@[hjo "lem_cm_zgraded_mul"]
theorem zGraded_mul_zGraded_subset (K : Type*) [CommRing K] [IsDomain K] (k d e : ℕ) :
    zGraded K k d * zGraded K k e ⊆ zGraded K k (d + e) := by
  rw [Set.mul_subset_iff]
  exact fun _ hG _ hH => mul_mem_zGraded hG hH

/-! ### The alphabet grading is direct -/

/-- **The alphabet grading is direct**: if `G_d ∈ Z^{(k+1)}_d` for every `d`, all but finitely many
of the `G_d` are `0`, and `∑_d G_d = 0`, then every `G_d` is `0`.

Fix a letter-monomial `x^α`. The coefficient of `G_d` there is `c^{(d)}y_{k+1}^{\,d-|α|}`, and it
vanishing for `|α| > d`, so the coefficient of the sum is a `𝕂(y₁, …, y_k)`-combination of powers of
`y_{k+1}` in which distinct `d` contribute distinct powers; the transcendence of `y_{k+1}`,
`HJO.Sym.eq_zero_of_sum_auxFracCastSucc_mul_yFrac_pow_eq_zero`, forces every `c^{(d)}` to vanish. -/
@[hjo "lem_cm_zgraded_direct"]
theorem eq_zero_of_sum_eq_zero_of_mem_zGraded {s : Finset ℕ}
    {F : ℕ → AuxAlphabetSeriesFrac K (k + 1)} (hF : ∀ d, F d ∈ zGraded K k d)
    (hs : ∀ d ∉ s, F d = 0) (hsum : ∑ d ∈ s, F d = 0) (d : ℕ) : F d = 0 := by
  classical
  by_cases hd : d ∈ s
  · refine MvPowerSeries.ext fun α => ?_
    rw [MvPowerSeries.coeff_zero]
    rcases lt_or_ge d (Finsupp.degree α) with hα | hα
    · exact coeff_eq_zero_of_mem_zGraded (hF d) hα
    set m := Finsupp.degree α with hm
    have hmem : ∀ d' ∈ s.filter (fun d' => m ≤ d'), d' ∈ s ∧ m ≤ d' := fun d' hd' =>
      Finset.mem_filter.1 hd'
    have h1 : ∑ d' ∈ s.filter (fun d' => m ≤ d'), MvPowerSeries.coeff α (F d') = 0 := by
      have h0 : ∑ d' ∈ s, MvPowerSeries.coeff α (F d') = 0 := by
        rw [← map_sum, hsum, map_zero]
      have h2 : ∑ d' ∈ s.filter (fun d' => ¬ m ≤ d'), MvPowerSeries.coeff α (F d') = 0 :=
        Finset.sum_eq_zero fun d' hd' => by
          have h4 := Finset.mem_filter.1 hd'
          exact coeff_eq_zero_of_mem_zGraded (hF d') (by omega)
      have h3 := Finset.sum_filter_add_sum_filter_not s (fun d' => m ≤ d')
        fun d' => MvPowerSeries.coeff α (F d')
      rw [h2, add_zero] at h3
      exact h3.trans h0
    have hchoice : ∀ d' ∈ s.filter (fun d' => m ≤ d'), ∃ c : AuxFrac K k,
        MvPowerSeries.coeff α (F d')
          = auxFracCastSucc K k c * yFrac K (Fin.last k) ^ (d' - m) := fun d' hd' =>
      exists_coeff_eq_of_mem_zGraded (hF d') α (by have := hmem d' hd'; omega)
    choose! c hc using hchoice
    have key : ∑ b ∈ (s.filter (fun d' => m ≤ d')).image (fun d' => d' - m),
        auxFracCastSucc K k (c (b + m)) * yFrac K (Fin.last k) ^ b = 0 := by
      rw [Finset.sum_image fun x hx y hy hxy => by
        have := hmem x hx; have := hmem y hy; omega]
      refine Eq.trans (Finset.sum_congr rfl fun d' hd' => ?_) h1
      rw [show d' - m + m = d' by have := hmem d' hd'; omega, ← hc d' hd']
    have hdt : d - m ∈ (s.filter (fun d' => m ≤ d')).image (fun d' => d' - m) :=
      Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hd, hα⟩)
    have hcd : c (d - m + m) = 0 :=
      eq_zero_of_sum_auxFracCastSucc_mul_yFrac_pow_eq_zero key hdt
    rw [show d - m + m = d by omega] at hcd
    rw [hc d (Finset.mem_filter.2 ⟨hd, hα⟩), hcd, map_zero, zero_mul]
  · exact hs d hd

/-! ### The alphabet-graded subring -/

/-- **The alphabet-graded subring** `Z^{(k+1)}`: the series that are finite sums `∑_{d ≥ 0}G_d` with
`G_d ∈ Z^{(k+1)}_d` for every `d` and `G_d = 0` for all but finitely many `d`. The finitely many
nonzero degrees are recorded by a `Finset`, and the sum is the sum over it; the family is required
to be graded at *every* degree, which costs nothing since `0` lies in every piece. That the sum
determines the family — so that the decomposition is a direct sum — is
`HJO.Sym.eq_zero_of_sum_eq_zero_of_mem_zGraded`. -/
@[hjo "def_cm_zring"]
def zRing (K : Type*) [CommRing K] [IsDomain K] (k : ℕ) : Set (AuxAlphabetSeriesFrac K (k + 1)) :=
  {G | ∃ (s : Finset ℕ) (F : ℕ → AuxAlphabetSeriesFrac K (k + 1)),
    (∀ d, F d ∈ zGraded K k d) ∧ (∀ d ∉ s, F d = 0) ∧ G = ∑ d ∈ s, F d}

/-- Membership in `Z^{(k+1)}`, unfolded. -/
theorem mem_zRing_iff :
    G ∈ zRing K k ↔ ∃ (s : Finset ℕ) (F : ℕ → AuxAlphabetSeriesFrac K (k + 1)),
      (∀ d, F d ∈ zGraded K k d) ∧ (∀ d ∉ s, F d = 0) ∧ G = ∑ d ∈ s, F d :=
  Iff.rfl

/-- Each graded piece lies in `Z^{(k+1)}`: a one-term sum. -/
theorem zGraded_subset_zRing (K : Type*) [CommRing K] [IsDomain K] (k d : ℕ) :
    zGraded K k d ⊆ zRing K k := by
  classical
  intro G hG
  refine ⟨{d}, fun d' => if d' = d then G else 0, fun d' => ?_, fun d' hd' => ?_, ?_⟩
  · rcases eq_or_ne d' d with rfl | h
    · simpa using hG
    · simpa [h] using zero_mem_zGraded
  · simp only [Finset.mem_singleton] at hd'
    simp [hd']
  · simp

/-! ### The exponent vectors of the merged alphabet -/

/-- A merged exponent vector in terms of its two parts: the total degree of `y_{k+1}^b x^α` in the
merged alphabet is `b + |α|`. -/
theorem degree_optionElim (b : ℕ) (α : ℕ →₀ ℕ) :
    Finsupp.degree (α.optionElim b) = b + Finsupp.degree α := by
  have h : α.optionElim b = Finsupp.single none b + α.mapDomain Option.some := by
    ext a
    cases a with
    | none =>
      rw [Finsupp.optionElim_apply_none, Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.mapDomain_of_notMem_range _ _ (by simp), add_zero]
    | some i =>
      rw [Finsupp.optionElim_apply_some, Finsupp.add_apply, Finsupp.single_eq_of_ne (by simp),
        Finsupp.mapDomain_apply (Option.some_injective ℕ), zero_add]
  rw [h, map_add, Finsupp.degree_single, Finsupp.degree_mapDomain]

/-- The total degree of a merged exponent vector splits as the exponent of `y_{k+1}` plus the total
degree of its letter part. -/
theorem degree_eq_add_degree_some (μ : Option ℕ →₀ ℕ) :
    Finsupp.degree μ = μ none + Finsupp.degree μ.some := by
  conv_lhs => rw [← Finsupp.optionElim_some μ]
  rw [degree_optionElim]

/-- Relabelling the letters along a permutation preserves the total degree: the image monomial has
the same letters counted with multiplicity. -/
theorem degree_equivMapDomain {σ τ : Type*} (e : σ ≃ τ) (ν : σ →₀ ℕ) :
    Finsupp.degree (Finsupp.equivMapDomain e ν) = Finsupp.degree ν := by
  rw [Finsupp.equivMapDomain_eq_mapDomain, Finsupp.degree_mapDomain]

/-- A merged exponent vector is determined by its two parts. -/
theorem optionElim_eq_iff {b : ℕ} {α : ℕ →₀ ℕ} {ν : Option ℕ →₀ ℕ} :
    α.optionElim b = ν ↔ α = ν.some ∧ b = ν none := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨h1, h2⟩ => ?_⟩
  · rw [← h, Finsupp.some_optionElim]
  · rw [← h, Finsupp.optionElim_apply_none]
  · rw [h1, h2, Finsupp.optionElim_some]

/-- Reindexing along a permutation and along its inverse are mutually inverse, as an equation solved
for the reindexed vector. -/
theorem equivMapDomain_symm_eq_iff {σ : Type*} (e : Equiv.Perm σ) (ν μ : σ →₀ ℕ) :
    Finsupp.equivMapDomain e.symm ν = μ ↔ ν = Finsupp.equivMapDomain e μ := by
  constructor
  · rintro rfl
    rw [← Finsupp.equivMapDomain_trans, Equiv.symm_trans_self, Finsupp.equivMapDomain_refl]
  · rintro rfl
    rw [← Finsupp.equivMapDomain_trans, Equiv.self_trans_symm, Finsupp.equivMapDomain_refl]

/-! ### The merged monomials and their coefficients -/

/-- The merged monomial `c z^ν`: the scalar `c` of the lower coefficient field times the monomial of
the merged alphabet with exponent vector `ν`, whose exponent of the distinguished letter `y_{k+1}`
is `ν none` and whose exponent of the letter `x_{i+1}` is `ν (some i)`. -/
noncomputable def zMonomial (K : Type*) [CommRing K] [IsDomain K] (k : ℕ)
    (ν : Option ℕ →₀ ℕ) (c : AuxFrac K k) : AuxAlphabetSeriesFrac K (k + 1) :=
  MvPowerSeries.monomial ν.some (auxFracCastSucc K k c * yFrac K (Fin.last k) ^ ν none)

/-- The merged letter `none` is the distinguished letter `y_{k+1}` of the merged alphabet. -/
theorem zMonomial_single_none (K : Type*) [CommRing K] [IsDomain K] (k : ℕ) :
    zMonomial K k (Finsupp.single none 1) 1
      = MvPowerSeries.C (yFrac K (Fin.last k)) := by
  rw [zMonomial, Finsupp.some_single_none, Finsupp.single_eq_same, map_one, one_mul, pow_one,
    MvPowerSeries.monomial_zero_eq_C_apply]

/-- The merged letter `some i` is the letter `x_{i+1}` of the alphabet. -/
theorem zMonomial_single_some (K : Type*) [CommRing K] [IsDomain K] (k i : ℕ) :
    zMonomial K k (Finsupp.single (some i) 1) 1 = MvPowerSeries.X i := by
  rw [zMonomial, Finsupp.some_single_some, Finsupp.single_eq_of_ne (by simp), map_one, one_mul,
    pow_zero, MvPowerSeries.X]

/-- The coefficient of the merged monomial `z^ν` in a series: the coefficient of `y_{k+1}^{ν none}`
in the coefficient of the series at the letter-monomial `x^{ν.some}`. For a member of a graded piece
this is the `c_α` of the `∑_α c_α y_k^{\,d-|α|}x^α`, well defined because `y_{k+1}` is
transcendental over `𝕂(y₁, …, y_k)`. -/
noncomputable def zCoeff (K : Type*) [CommRing K] [IsDomain K] (k : ℕ)
    (G : AuxAlphabetSeriesFrac K (k + 1)) (ν : Option ℕ →₀ ℕ) : AuxFrac K k :=
  yFracCoeff K k (MvPowerSeries.coeff ν.some G) (ν none)

/-- The merged coefficients of a merged monomial: `c` at its own exponent vector and `0` at every
other, so the two constructions are mutually inverse on monomials. -/
theorem zCoeff_zMonomial (ν μ : Option ℕ →₀ ℕ) (c : AuxFrac K k) :
    zCoeff K k (zMonomial K k ν c) μ = if μ = ν then c else 0 := by
  classical
  rw [zCoeff, zMonomial]
  rcases eq_or_ne μ.some ν.some with h | h
  · rw [h, MvPowerSeries.coeff_monomial_same, yFracCoeff_mul_yFrac_pow]
    rcases eq_or_ne (μ none) (ν none) with h2 | h2
    · have hμν : μ = ν := by
        ext a
        cases a with
        | none => exact h2
        | some i => rw [← Finsupp.some_apply, ← Finsupp.some_apply, h]
      rw [ite_eq_left h2, ite_eq_left hμν]
    · rw [ite_eq_right h2, ite_eq_right fun hμν => h2 (by rw [hμν])]
  · rw [MvPowerSeries.coeff_monomial_ne h, yFracCoeff_zero,
      ite_eq_right fun hμν => h (by rw [hμν])]

/-- Every coefficient of a member of a graded piece is a polynomial in `y_{k+1}` over the lower
coefficient field: below the degree it is a single scaled power, above it `0`. This is what makes
the merged coefficients of `HJO.Sym.zCoeff` meaningful on `Z^{(k+1)}_d`. -/
theorem coeff_mem_range_yFracEval_of_mem_zGraded (hG : G ∈ zGraded K k d) (α : ℕ →₀ ℕ) :
    MvPowerSeries.coeff α G ∈ (yFracEval K k).range := by
  rcases lt_or_ge d (Finsupp.degree α) with hα | hα
  · rw [coeff_eq_zero_of_mem_zGraded hG hα]
    exact zero_mem _
  · obtain ⟨c, hc⟩ := exists_coeff_eq_of_mem_zGraded hG α (b := d - Finsupp.degree α) (by omega)
    exact RingHom.mem_range.2
      ⟨Polynomial.C c * Polynomial.X ^ (d - Finsupp.degree α), by
        rw [yFracEval_C_mul_X_pow, hc]⟩

/-- Every coefficient of a member of `Z^{(k+1)}` is a polynomial in `y_{k+1}` over the lower
coefficient field: a finite sum of the graded case. -/
theorem coeff_mem_range_yFracEval_of_mem_zRing (hG : G ∈ zRing K k) (α : ℕ →₀ ℕ) :
    MvPowerSeries.coeff α G ∈ (yFracEval K k).range := by
  obtain ⟨s, F, hF, -, rfl⟩ := hG
  rw [map_sum]
  exact sum_mem fun d _ => coeff_mem_range_yFracEval_of_mem_zGraded (hF d) α

/-- The merged coefficients are additive on the series whose coefficients are polynomial in
`y_{k+1}`, in particular on `Z^{(k+1)}`. -/
theorem zCoeff_add (hG : ∀ α, MvPowerSeries.coeff α G ∈ (yFracEval K k).range)
    (hH : ∀ α, MvPowerSeries.coeff α H ∈ (yFracEval K k).range) (μ : Option ℕ →₀ ℕ) :
    zCoeff K k (G + H) μ = zCoeff K k G μ + zCoeff K k H μ := by
  rw [zCoeff, zCoeff, zCoeff, map_add, yFracCoeff_add_of_mem_range (hG _) (hH _)]

/-- The merged coefficients are homogeneous for the scalars of the lower coefficient field. -/
theorem zCoeff_auxFracCastSucc_smul (hG : ∀ α, MvPowerSeries.coeff α G ∈ (yFracEval K k).range)
    (a : AuxFrac K k) (μ : Option ℕ →₀ ℕ) :
    zCoeff K k (auxFracCastSucc K k a • G) μ = a * zCoeff K k G μ := by
  rw [zCoeff, zCoeff, MvPowerSeries.coeff_smul, yFracCoeff_auxFracCastSucc_mul (hG _)]

/-- A member of `Z^{(k+1)}_d` has merged coefficients only in merged degree `d`: that is what "a
formal combination of the monomials of total degree `d` in the merged alphabet" says about the
coefficients. -/
theorem zCoeff_eq_zero_of_mem_zGraded (hG : G ∈ zGraded K k d) {μ : Option ℕ →₀ ℕ}
    (hμ : Finsupp.degree μ ≠ d) : zCoeff K k G μ = 0 := by
  rw [zCoeff]
  rcases lt_or_ge d (Finsupp.degree μ.some) with h | h
  · rw [coeff_eq_zero_of_mem_zGraded hG h, yFracCoeff_zero]
  · obtain ⟨c, hc⟩ :=
      exists_coeff_eq_of_mem_zGraded hG μ.some (b := d - Finsupp.degree μ.some) (by omega)
    have hd : μ none ≠ d - Finsupp.degree μ.some := by
      have := degree_eq_add_degree_some μ
      omega
    rw [hc, yFracCoeff_mul_yFrac_pow, ite_eq_right hd]

/-- A member of `Z^{(k+1)}` has merged coefficients only in boundedly many merged degrees: the
finitely many degrees its decomposition uses. -/
theorem exists_zCoeff_eq_zero_of_mem_zRing (hG : G ∈ zRing K k) :
    ∃ N : ℕ, ∀ μ : Option ℕ →₀ ℕ, N < Finsupp.degree μ → zCoeff K k G μ = 0 := by
  obtain ⟨s, F, hF, -, rfl⟩ := hG
  refine ⟨s.sup id, fun μ hμ => ?_⟩
  rw [zCoeff, map_sum,
    yFracCoeff_sum_of_mem_range fun d _ => coeff_mem_range_yFracEval_of_mem_zGraded (hF d) _]
  refine Finset.sum_eq_zero fun d hd => ?_
  refine zCoeff_eq_zero_of_mem_zGraded (hF d) (μ := μ) fun h => ?_
  have := Finset.le_sup (f := id) hd
  simp only [id] at this
  omega

/-! ### Permuting the merged variables -/

/-- **Permuting the merged variables**: for a permutation `ρ` of the merged alphabet
`y_{k+1}, x₁, x₂, …`, the map `ŝ_ρ` relabelling the letters of each merged monomial along `ρ` and
acting on a formal combination of merged monomials coefficientwise. The coefficient at the
letter-monomial `x^α` is `∑_b c_{ρ^{-1}(b,α)}y_{k+1}^b`, the merged coefficients of
`HJO.Sym.zCoeff` read at the relabelled exponent vectors.

Such a relabelling is not induced by any substitution in `P°_{k+1}`, since `y_{k+1}` lies in the
coefficient field and the letters do not; what makes the definition possible is that on `Z^{(k+1)}`
the coefficient at `x^α` *is* a polynomial in `y_{k+1}` over `𝕂(y₁, …, y_k)`, uniquely so because
`y_{k+1}` is transcendental. Off `Z^{(k+1)}` the value is accordingly not meaningful, and every
statement about `HJO.Sym.zPerm` below carries a membership hypothesis; the `ŝ_ρ` is this
map at a permutation fixing all but finitely many letters. -/
@[hjo "def_cm_zperm"]
noncomputable def zPerm (K : Type*) [CommRing K] [IsDomain K] (k : ℕ)
    (ρ : Equiv.Perm (Option ℕ)) (G : AuxAlphabetSeriesFrac K (k + 1)) :
    AuxAlphabetSeriesFrac K (k + 1) := fun α =>
  ∑ᶠ b : ℕ, auxFracCastSucc K k (zCoeff K k G (Finsupp.equivMapDomain ρ.symm (α.optionElim b)))
    * yFrac K (Fin.last k) ^ b

/-- The coefficients of `ŝ_ρ G`, by definition. -/
theorem coeff_zPerm (ρ : Equiv.Perm (Option ℕ)) (G : AuxAlphabetSeriesFrac K (k + 1))
    (α : ℕ →₀ ℕ) :
    MvPowerSeries.coeff α (zPerm K k ρ G)
      = ∑ᶠ b : ℕ, auxFracCastSucc K k
            (zCoeff K k G (Finsupp.equivMapDomain ρ.symm (α.optionElim b)))
          * yFrac K (Fin.last k) ^ b :=
  rfl

/-- **`ŝ_ρ` relabels the merged monomials**: it carries `c z^ν` to `c z^{ρν}`, which is the
relabelling "carrying each monomial `∏_i z^{(k)}_{j_i}` to `∏_i z^{(k)}_{ρ(j_i)}`". -/
@[hjo "def_cm_zperm"]
theorem zPerm_zMonomial (ρ : Equiv.Perm (Option ℕ)) (ν : Option ℕ →₀ ℕ) (c : AuxFrac K k) :
    zPerm K k ρ (zMonomial K k ν c) = zMonomial K k (Finsupp.equivMapDomain ρ ν) c := by
  classical
  set ν' := Finsupp.equivMapDomain ρ ν with hν'
  refine MvPowerSeries.ext fun α => ?_
  have hterm : ∀ b : ℕ,
      auxFracCastSucc K k (zCoeff K k (zMonomial K k ν c)
            (Finsupp.equivMapDomain ρ.symm (α.optionElim b)))
          * yFrac K (Fin.last k) ^ b
        = if α = ν'.some ∧ b = ν' none then
            auxFracCastSucc K k c * yFrac K (Fin.last k) ^ ν' none else 0 := by
    intro b
    have hiff : Finsupp.equivMapDomain ρ.symm (α.optionElim b) = ν ↔
        (α = ν'.some ∧ b = ν' none) := by
      rw [equivMapDomain_symm_eq_iff, ← hν', optionElim_eq_iff]
    by_cases hc : α = ν'.some ∧ b = ν' none
    · rw [zCoeff_zMonomial, ite_eq_left (hiff.2 hc), ite_eq_left hc, hc.2]
    · rw [zCoeff_zMonomial, ite_eq_right fun h => hc (hiff.1 h), ite_eq_right hc, map_zero,
        zero_mul]
  rw [coeff_zPerm, finsum_congr hterm, zMonomial]
  by_cases hα : α = ν'.some
  · rw [finsum_eq_single _ (ν' none) fun x hx => ite_eq_right fun h => hx h.2,
      ite_eq_left ⟨hα, rfl⟩, hα, MvPowerSeries.coeff_monomial_same]
  · rw [finsum_eq_single _ 0 fun x _ => ite_eq_right fun h => hα h.1, ite_eq_right fun h => hα h.1,
      MvPowerSeries.coeff_monomial_ne hα]

/-- The sum defining a coefficient of `ŝ_ρ G` has finite support once the merged coefficients of `G`
vanish in high merged degree: relabelling preserves the merged degree, so a term at `b` can only
survive while `b + |α|` stays within the bound. -/
theorem support_finite_of_zCoeff_eq_zero (ρ : Equiv.Perm (Option ℕ)) {N : ℕ} (α : ℕ →₀ ℕ)
    (h : ∀ μ : Option ℕ →₀ ℕ, N < Finsupp.degree μ → zCoeff K k G μ = 0) :
    (Function.support fun b : ℕ => auxFracCastSucc K k
          (zCoeff K k G (Finsupp.equivMapDomain ρ.symm (α.optionElim b)))
        * yFrac K (Fin.last k) ^ b).Finite := by
  refine (Set.finite_Iic N).subset fun b hb => ?_
  simp only [Set.mem_Iic]
  by_contra hbN
  refine hb ?_
  change auxFracCastSucc K k (zCoeff K k G (Finsupp.equivMapDomain ρ.symm (α.optionElim b)))
      * yFrac K (Fin.last k) ^ b = 0
  rw [show zCoeff K k G (Finsupp.equivMapDomain ρ.symm (α.optionElim b)) = 0 from
    h _ (by rw [degree_equivMapDomain, degree_optionElim]; omega), map_zero, zero_mul]

/-- The coefficients of `ŝ_ρ G` for `G` in a graded piece, at the letter-monomials the
multi-indices reach: a single scaled power of `y_{k+1}`, with the exponent `b` the one satisfying
`b + |α| = d`. Together with `HJO.Sym.coeff_zPerm_eq_zero_of_mem_zGraded` this is the membership
`ŝ_ρ G ∈ Z^{(k+1)}_d`. -/
theorem coeff_zPerm_of_mem_zGraded (ρ : Equiv.Perm (Option ℕ)) (hG : G ∈ zGraded K k d)
    {α : ℕ →₀ ℕ} (hα : Finsupp.degree α ≤ d) :
    MvPowerSeries.coeff α (zPerm K k ρ G)
      = auxFracCastSucc K k (zCoeff K k G
            (Finsupp.equivMapDomain ρ.symm (α.optionElim (d - Finsupp.degree α))))
          * yFrac K (Fin.last k) ^ (d - Finsupp.degree α) := by
  rw [coeff_zPerm]
  refine finsum_eq_single _ (d - Finsupp.degree α) fun b hb => ?_
  rw [zCoeff_eq_zero_of_mem_zGraded hG
    (by rw [degree_equivMapDomain, degree_optionElim]; omega), map_zero, zero_mul]

/-- The coefficients of `ŝ_ρ G` for `G` in a graded piece, beyond the degree: `0`, as for `G`
itself. -/
theorem coeff_zPerm_eq_zero_of_mem_zGraded (ρ : Equiv.Perm (Option ℕ)) (hG : G ∈ zGraded K k d)
    {α : ℕ →₀ ℕ} (hα : d < Finsupp.degree α) : MvPowerSeries.coeff α (zPerm K k ρ G) = 0 := by
  have hzero : ∀ b : ℕ, auxFracCastSucc K k
      (zCoeff K k G (Finsupp.equivMapDomain ρ.symm (α.optionElim b)))
        * yFrac K (Fin.last k) ^ b = 0 := fun b => by
    rw [zCoeff_eq_zero_of_mem_zGraded hG
      (by rw [degree_equivMapDomain, degree_optionElim]; omega), map_zero, zero_mul]
  rw [coeff_zPerm, finsum_eq_single _ 0 fun b _ => hzero b]
  exact hzero 0

/-- **`ŝ_ρ` is additive on `Z^{(k+1)}`**: the merged coefficients add, and the sums defining the
coefficients of the two images have finite support, so they may be added term by term. -/
@[hjo "def_cm_zperm"]
theorem zPerm_add_of_mem_zRing (ρ : Equiv.Perm (Option ℕ)) (hG : G ∈ zRing K k)
    (hH : H ∈ zRing K k) : zPerm K k ρ (G + H) = zPerm K k ρ G + zPerm K k ρ H := by
  obtain ⟨N, hN⟩ := exists_zCoeff_eq_zero_of_mem_zRing hG
  obtain ⟨N', hN'⟩ := exists_zCoeff_eq_zero_of_mem_zRing hH
  refine MvPowerSeries.ext fun α => ?_
  rw [map_add, coeff_zPerm, coeff_zPerm, coeff_zPerm,
    finsum_congr fun b => by
      rw [zCoeff_add (coeff_mem_range_yFracEval_of_mem_zRing hG)
        (coeff_mem_range_yFracEval_of_mem_zRing hH), map_add, add_mul]]
  exact finsum_add_distrib (support_finite_of_zCoeff_eq_zero ρ α hN)
    (support_finite_of_zCoeff_eq_zero ρ α hN')

/-- **`ŝ_ρ` is `𝕂(y₁, …, y_k)`-homogeneous on `Z^{(k+1)}`**, the scalars acting on `P°_{k+1}`
through `HJO.Sym.auxFracCastSucc`: with `HJO.Sym.zPerm_add_of_mem_zRing` this is the linearity
of `ŝ_ρ`. -/
@[hjo "def_cm_zperm"]
theorem zPerm_auxFracCastSucc_smul_of_mem_zRing (ρ : Equiv.Perm (Option ℕ)) (a : AuxFrac K k)
    (hG : G ∈ zRing K k) :
    zPerm K k ρ (auxFracCastSucc K k a • G) = auxFracCastSucc K k a • zPerm K k ρ G := by
  refine MvPowerSeries.ext fun α => ?_
  rw [MvPowerSeries.coeff_smul, coeff_zPerm, coeff_zPerm,
    finsum_congr fun b => by
      rw [zCoeff_auxFracCastSucc_smul (coeff_mem_range_yFracEval_of_mem_zRing hG), map_mul,
        mul_assoc]]
  exact (mul_finsum _ _).symm

end HJO.Sym
