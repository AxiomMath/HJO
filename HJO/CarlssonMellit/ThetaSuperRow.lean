/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Classical.ThetaHsymm
public import HJO.CarlssonMellit.SuperSchur
public import HJO.Classical.HsymmGessel
public import HJO.SignExtraction.Basic
public import HJO.SignExtraction.Words
public meta import HJO.Attr

/-! # The plethysm of a complete homogeneous function is a super fundamental

`HJO.ParkingFunctions.realisation_thetaLambda_completeHomog`: for a realisation `ι` and every `r`,
`ι(θ₀(h_r)) = F̃_{r,∅}`.

## Main definitions

* `HJO.Sym.thetaLambda`: the scaling `θ₀` of `HJO.Sweep.theta` read on `Λ` itself.
* `HJO.Sym.superCode`, `HJO.Sym.superDecode`: the order isomorphism `𝒜 ≃ ℕ`, `(a, ε) ↦ 2a + ε`.
* `HJO.Sym.superPosExp`, `HJO.Sym.superNegExp`: the exponent vectors of the absolute values of the
  positive and of the negative letters of a super word — the words `u` and `w`, recorded as
  multisets.
* `HJO.Sym.superWordOfPair`: the super word a pair of exponent vectors comes from.

## Main results

* `HJO.Sweep.theta_C`: `thetaLambda` is `HJO.Sweep.theta` restricted to `V_0`, which is what makes
  `ι(θ₀(f))` — an expression asking for an element of `Λ` — mean `ι(thetaLambda q f)`.
* `HJO.Sym.thetaLambda_completeHomog`: `HJO.Sweep.theta_completeHomog` read on `Λ`.
* `HJO.Sym.sum_prod_superScalar_eq_sum_superSplits`: the bijection, between the super
  ascending words of a given exponent vector and the splittings of that vector whose second member
  is squarefree.
* `HJO.ParkingFunctions.sum_gessel_eq_superFundamental`: the identity with the realisation removed,
  `∑_{s+t=r}q^s(-1)^tF_{s,∅}F_{t,\{1,…,t-1\}} = F̃_{r,∅}`.
* `HJO.ParkingFunctions.realisation_thetaLambda_completeHomog`.

## Implementation notes

*`θ₀` is stated on `Λ`, not on the total space, and the two readings are bridged rather than left
parallel.* `HJO.Sweep.theta` is an endomorphism of the *total space* `HJO.Sweep.Total`, in which
`V_0` is the image of `MvPolynomial.C`; a realisation is a map out of `Λ`, so the expression
`ι(θ₀(h_r))` does not even typecheck against `HJO.Sweep.theta` — it asks for the element of `Λ` that
`θ₀` produces. `HJO.Sym.thetaLambda` is that element's producer, the diagonal substitution
`HJO.Sym.diagScale` scaling `p_k` by `q^k - 1`. It is **not** a second encoding of `θ`: the two are
identified by `HJO.Sweep.theta_C`, `θ(C f) = C(thetaLambda q f)`, proved below by induction on `f`,
so every statement about one transports to the other and no fact is available on one side only. For
the same reason `HJO.Sweep.theta_completeHomog` is not reproved here:
`HJO.Sym.thetaLambda_completeHomog` is the *same* instance of the general principle
`HJO.CreationSeeds.completeHomog_scaled` that `HJO.Sweep.theta_completeHomog` is, taken at `φ` the
identity of `Λ` rather than at `φ = MvPolynomial.C`, so the generating-series argument behind it is
run once, in `HJO.Classical.ThetaHsymm`, and not again.

*The proof is coefficientwise, not by truncation.* The bijection sends a super word of
length `r` to a pair `(u, w)` of words of lengths `s` and `t` with `s + t = r`, and those lengths
vary with the word; carried out on tuples it would be a bijection between a sigma-type of
`Fin s → ℕ` and `Fin r → 𝒜`, with every step transported along an equality of `Fin` types. Read on
one coefficient the same bijection is between super words and *pairs of exponent vectors*
`(d₁, d₂)` with `d₁ + d₂ = d`, which carry no length at all: the degrees `s` and `t` are read off
them (`HJO.Sym.degree_superPosExp`) rather than fixed in advance. The two coefficient formulas the
comparison runs on are `HJO.ParkingFunctions.coeff_gessel_empty` and
`HJO.ParkingFunctions.coeff_gessel_Ico` on one side — the exponent vectors of total degree `n`, and
the squarefree ones among them — and `HJO.Sym.coeff_superFundamental_empty` on the other.

*The super alphabet is coded by `ℕ` rather than sorted in its own right.* The inverse of the
bijection has to produce the weakly increasing super word with a prescribed multiset of letters, and
`HJO.SignExtraction.Words` already builds and characterises that word over `ℕ`
(`HJO.Sym.wordOfExponent`, `HJO.Sym.eq_of_wordExponent_eq`). `HJO.Sym.superCode` is the order
isomorphism `(a, ε) ↦ 2a + ε` — the order `1 < 1̄ < 2 < 2̄ < ⋯` of `HJO.Sym.SuperLetter.lt_iff` is
the order of `ℕ` read this way — so that machinery is reused through it instead of being redone for
`𝒜`; `HJO.Sym.superCodeExp` is the translation of a pair `(d₁, d₂)` into the multiset of super
letters, the even codes carrying `d₁` and the odd ones `d₂`.

*At `S = ∅` the three clauses of `HJO.Sym.superFundamental` say: weakly increasing, with no repeated
negative letter.* A repetition of a positive letter is allowed at every step and one of a negative
letter at none, which is `HJO.Sym.IsSuperAscendingWord.card_filter_le_one`; that the negative
letters are therefore distinct is exactly the squarefreeness of `d₂`.

*`𝕜 ⊇ ℚ` is inherited and not an addition.* `HJO.Sym.completeHomog` and `HJO.Sym.elemSymm` are
*defined* by Newton's identities, which divide by `n`, so `[Algebra ℚ K]` is already carried by
`HJO.Sweep.theta_completeHomog`, by `HJO.ParkingFunctions.realisation_completeHomog` and by
`HJO.ParkingFunctions.realisation_elemSymm`. Nothing in this file needs it beyond naming `h_r` and
`e_t`: the combinatorial half, `HJO.ParkingFunctions.sum_gessel_eq_superFundamental`, is stated over
an arbitrary commutative ring.

*The hypothesis `r ≥ 1` is not needed*, and neither is the positivity of the letters of `u` and `w`.
At `r = 0` the left side is `ι(θ₀(h_0)) = ι(θ₀(1)) = 1` and the right side is `F̃_{0,∅}`, the sum of
`z_v` over the one super word of length `0`, whose monomial is the empty product `1`
(`HJO.Sym.superMonomial_zero`); the two agree, and no step of the proof looks at positivity — the
`j`-sum of `HJO.Sweep.theta_completeHomog` at `r = 0` is its single term `h_0e_0`. Absolute values
are indexed from `0` throughout, as everywhere in this part of the library, so the positivity
condition `u ∈ ℤ_{>0}^s` is vacuous.

## References

Lemma `HJO.ParkingFunctions.realisation_thetaLambda_completeHomog`. Its statement uses
`HJO.Sym.Lambda`, `HJO.Sym.AlphabetSeries`, `HJO.Sym.completeHomog`, `HJO.Sym.IsRealisation`,
`HJO.Sweep.theta` and `HJO.Sym.superFundamental`; its proof uses `HJO.Sweep.theta_completeHomog`
(`HJO.Sweep.theta_completeHomog`, reread here as `HJO.Sym.thetaLambda_completeHomog`),
`HJO.ParkingFunctions.realisation_completeHomog`, `HJO.ParkingFunctions.realisation_elemSymm`,
together with `HJO.Sym.elemSymm`, `HJO.ParkingFunctions.gessel`, `HJO.Sym.IsAscendingWord`,
`HJO.Sym.wordMonomial`, `HJO.Sym.SuperLetter.lt_iff`, `HJO.Sym.superVar` and
`HJO.Sym.superMonomial`. See also E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J.
Amer. Math. Soc. **31** (2018) 661--697, Section 3.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### The scaling of the alphabet read on `Λ` -/

section ThetaLambda

variable {K : Type*} [CommRing K]

/-- **`θ₀` read on `Λ` itself**: the `𝕜`-algebra endomorphism of `Λ` scaling `p_r` by `q^r - 1`.

`HJO.Sweep.theta` defines `θ_k` on the total space `HJO.Sweep.Total`, where `V_0` is the image of
`MvPolynomial.C`; `HJO.Sweep.theta_C` says that this map is its restriction to `V_0` read through
that inclusion, so that `ι(θ₀(f))` — which asks for an element of `Λ` — is `ι(thetaLambda q f)`. -/
noncomputable def thetaLambda (q : K) : Lambda K →ₐ[K] Lambda K :=
  diagScale fun i => q ^ (i + 1) - 1

/-- `θ₀` fixes the constants, being an algebra map. -/
@[simp]
theorem thetaLambda_C (q : K) (a : K) : thetaLambda q (MvPolynomial.C a) = MvPolynomial.C a :=
  diagScale_C _ a

/-- `θ₀` multiplies the generator of index `i` by `q^{i+1} - 1`. -/
@[simp]
theorem thetaLambda_X (q : K) (i : ℕ) :
    thetaLambda q (MvPolynomial.X i) = MvPolynomial.C (q ^ (i + 1) - 1) * MvPolynomial.X i :=
  diagScale_X _ i

/-- **The defining property of `θ₀`**: it scales the power sum `p_k` by `q^k - 1` for `k ≥ 1`. -/
theorem thetaLambda_powerSum (q : K) {k : ℕ} (hk : 0 < k) :
    thetaLambda q (powerSum K k) = (MvPolynomial.C q ^ k - 1) * powerSum K k := by
  rw [thetaLambda, diagScale_powerSum, show k - 1 + 1 = k from by omega, map_sub, map_pow, map_one]

end ThetaLambda

end HJO.Sym

namespace HJO.Sweep

variable {L : Type*} [CommRing L]

/-- The `L`-algebra map into the total space is the double inclusion of constants: `L` enters
through `Λ`, which enters through `MvPolynomial.C`. -/
theorem algebraMap_total_eq (a : L) :
    algebraMap L (Total L) a = MvPolynomial.C (MvPolynomial.C a) := by
  rw [IsScalarTower.algebraMap_apply L (Sym.Lambda L) (Total L), MvPolynomial.algebraMap_eq,
    MvPolynomial.algebraMap_eq]

/-- `θ_k` on the generator `p_{j+1}` of `V_0`, read off `HJO.Sweep.theta`. -/
theorem theta_C_X (q : L) (j : ℕ) :
    theta q (MvPolynomial.C (MvPolynomial.X j) : Total L)
      = algebraMap L (Total L) (q ^ (j + 1) - 1) * MvPolynomial.C (MvPolynomial.X j) := by
  rw [theta, MvPolynomial.aevalTower_C, MvPolynomial.aeval_X]

/-- **`θ_k` restricted to `V_0` is `HJO.Sym.thetaLambda`**: the `θ₀` acts on the
symmetric functions, and `V_0` is the image of `MvPolynomial.C`, so the two maps agree through that
inclusion. This is what lets the `ι(θ₀(f))` be read as `ι(thetaLambda q f)`. -/
theorem theta_C (q : L) (f : Sym.Lambda L) :
    theta q (MvPolynomial.C f) = MvPolynomial.C (Sym.thetaLambda q f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [Sym.thetaLambda_C, theta, MvPolynomial.aevalTower_C, MvPolynomial.aeval_C,
      algebraMap_total_eq]
  | add p p' hp hp' => rw [MvPolynomial.C_add, map_add, map_add, hp, hp', MvPolynomial.C_add]
  | mul_X p j hp =>
    rw [MvPolynomial.C_mul, map_mul, hp, theta_C_X, map_mul, Sym.thetaLambda_X,
      algebraMap_total_eq, MvPolynomial.C_mul, MvPolynomial.C_mul]

end HJO.Sweep

namespace HJO.Sym

/-! ### `HJO.Sweep.theta_completeHomog` read on `Λ` -/

/-- **`HJO.Sweep.theta_completeHomog` on `Λ`**: `θ₀(h_r) = ∑_{s+t=r}q^s(-1)^t h_s e_t`.

This is `HJO.CreationSeeds.completeHomog_scaled` at `φ` the identity of `Λ` and `ψ = θ₀`, the
scaling hypothesis being `thetaLambda_powerSum`; the version of `HJO.Sweep.theta_completeHomog` on
the total space is the same instance taken at `φ = MvPolynomial.C`. -/
theorem thetaLambda_completeHomog {K : Type*} [CommRing K] [Algebra ℚ K] (q : K) (r : ℕ) :
    thetaLambda q (completeHomog K r)
      = ∑ j ∈ range (r + 1), MvPolynomial.C q ^ j * (-1) ^ (r - j) *
          (completeHomog K j * elemSymm K (r - j)) := by
  have h := CreationSeeds.completeHomog_scaled (RingHom.id (Lambda K))
    (thetaLambda q).toRingHom (MvPolynomial.C q) (fun k hk => thetaLambda_powerSum q hk) r
  simpa using h

/-! ### Coding the super alphabet by the natural numbers -/

/-- **The code of a super letter**: twice its absolute value, and one more when it is negative.
The order `1 < 1̄ < 2 < 2̄ < ⋯` of `HJO.Sym.SuperLetter.lt_iff` is `0 < 1 < 2 < 3 < ⋯` read this
way, so the code is a strictly increasing bijection onto `ℕ` — which is what lets the sorting of
words over `ℕ` be reused for words over the alphabet, rather than redone. -/
def superCode (α : SuperLetter) : ℕ := 2 * α.absVal + cond (ofLex α).2 1 0

/-- The code of a positive letter is twice its absolute value. -/
@[simp]
theorem superCode_of_isPositive {α : SuperLetter} (h : α.IsPositive) :
    superCode α = 2 * α.absVal := by
  rw [superCode, show (ofLex α).2 = false from h, Bool.cond_false, add_zero]

/-- The code of a negative letter is one more than twice its absolute value. -/
@[simp]
theorem superCode_of_isNegative {α : SuperLetter} (h : α.IsNegative) :
    superCode α = 2 * α.absVal + 1 := by
  rw [superCode, show (ofLex α).2 = true from h, Bool.cond_true]

/-- The code of a letter lies in the two-element window of its absolute value. -/
theorem superCode_bounds (α : SuperLetter) :
    2 * α.absVal ≤ superCode α ∧ superCode α ≤ 2 * α.absVal + 1 := by
  by_cases h : α.IsNegative
  · rw [superCode_of_isNegative h]; omega
  · rw [superCode_of_isPositive ((SuperLetter.isPositive_iff_not_isNegative α).2 h)]; omega

/-- The absolute value of a letter is read off its code. -/
theorem absVal_eq_superCode_div_two (α : SuperLetter) : α.absVal = superCode α / 2 := by
  have h := superCode_bounds α
  omega

/-- A letter is negative exactly when its code is odd. -/
theorem isNegative_iff_superCode_mod_two (α : SuperLetter) :
    α.IsNegative ↔ superCode α % 2 = 1 := by
  refine ⟨fun h => by rw [superCode_of_isNegative h]; omega, fun h => ?_⟩
  by_contra hn
  rw [superCode_of_isPositive ((SuperLetter.isPositive_iff_not_isNegative α).2 hn)] at h
  omega

/-- **The letter of a code**: the inverse of `HJO.Sym.superCode`, reading the parity of the code as
the sign and its half as the absolute value. -/
def superDecode (m : ℕ) : SuperLetter := SuperLetter.mk (m / 2) (decide (m % 2 = 1))

/-- The absolute value of the letter of a code is half the code. -/
@[simp]
theorem absVal_superDecode (m : ℕ) : (superDecode m).absVal = m / 2 :=
  SuperLetter.absVal_mk _ _

/-- The letter of a code is negative exactly when the code is odd. -/
theorem isNegative_superDecode_iff (m : ℕ) : (superDecode m).IsNegative ↔ m % 2 = 1 := by
  simp only [SuperLetter.IsNegative, superDecode, SuperLetter.sign_mk, decide_eq_true_eq]

/-- Decoding inverts coding on the codes. -/
@[simp]
theorem superCode_superDecode (m : ℕ) : superCode (superDecode m) = m := by
  by_cases h : m % 2 = 1
  · rw [superCode_of_isNegative ((isNegative_superDecode_iff m).2 h), absVal_superDecode]
    omega
  · have hp : (superDecode m).IsPositive :=
      (SuperLetter.isPositive_iff_not_isNegative _).2 fun hc =>
        h ((isNegative_superDecode_iff m).1 hc)
    rw [superCode_of_isPositive hp, absVal_superDecode]
    omega

/-- Coding inverts decoding on the letters. -/
@[simp]
theorem superDecode_superCode (α : SuperLetter) : superDecode (superCode α) = α := by
  refine SuperLetter.ext (by rw [absVal_superDecode, absVal_eq_superCode_div_two]) ?_
  by_cases h : α.IsNegative
  · have h' : (ofLex α).2 = true := h
    rw [h', superDecode, SuperLetter.sign_mk, decide_eq_true_eq]
    exact (isNegative_iff_superCode_mod_two α).1 h
  · have hp : (ofLex α).2 = false := (SuperLetter.isPositive_iff_not_isNegative α).2 h
    rw [hp, superDecode, SuperLetter.sign_mk, decide_eq_false_iff_not]
    exact fun hc => h ((isNegative_iff_superCode_mod_two α).2 hc)

/-- **The code is strictly increasing**: `HJO.Sym.SuperLetter.lt_iff` compares absolute values first
and puts the positive letter of an absolute value below the negative one, which is the comparison of
`2a` and `2a + 1`. -/
theorem superCode_strictMono : StrictMono superCode := by
  intro α β hlt
  have hα := superCode_bounds α
  have hβ := superCode_bounds β
  rcases SuperLetter.lt_iff.1 hlt with h | ⟨heq, hpα, hnβ⟩
  · omega
  · rw [superCode_of_isPositive hpα, superCode_of_isNegative hnβ, heq]
    omega

/-- Distinct letters have distinct codes. -/
theorem superCode_injective : Function.Injective superCode :=
  superCode_strictMono.injective

/-- **Decoding is increasing**, the code being a strictly increasing bijection. -/
theorem superDecode_monotone : Monotone superDecode := by
  intro m m' h
  by_contra hc
  have h2 := superCode_strictMono (lt_of_not_ge hc)
  rw [superCode_superDecode, superCode_superDecode] at h2
  omega

/-- A super word is the decoding of its coded word: the two maps are inverse. -/
theorem superDecode_comp_superCode {n : ℕ} (v : Fin n → SuperLetter) :
    (fun i => superDecode (superCode (v i))) = v :=
  funext fun i => superDecode_superCode (v i)

/-! ### Exponent vectors: relabelling, degree, and the two parts of a super word -/

section ExponentVectors

/-- A letter is negative exactly when it is not positive, which is the form the splitting of the
positions of a super word needs. -/
theorem isNegative_iff_not_isPositive (α : SuperLetter) : α.IsNegative ↔ ¬α.IsPositive := by
  rw [SuperLetter.isPositive_iff_not_isNegative, not_not]

/-- The exponent vector of a relabelled word is the relabelling of its exponent vector. -/
theorem wordExponent_map {n : ℕ} (g : ℕ → ℕ) (w : Fin n → ℕ) :
    wordExponent (fun i => g (w i)) = Finsupp.mapDomain g (wordExponent w) := by
  rw [wordExponent, wordExponent, Finsupp.mapDomain_finsetSum]
  exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_single.symm

/-- The exponent vector of a word of length `n` has total degree `n`. -/
theorem degree_wordExponent {n : ℕ} (w : Fin n → ℕ) : (wordExponent w).degree = n := by
  rw [wordExponent, map_sum]
  simp

/-- The number of letters of an exponent vector, with multiplicity, is its total degree. This is
the form in which `HJO.Sym.wordOfExponent`'s hypothesis is checked. -/
theorem card_toMultiset_eq_degree (d : ℕ →₀ ℕ) :
    Multiset.card (Finsupp.toMultiset d) = d.degree := by
  rw [Finsupp.card_toMultiset, Finsupp.degree_apply, Finsupp.sum]
  rfl

/-- Splitting a sum over the positions of a super word by the sign of the letter. -/
theorem sum_filter_isPositive_add_sum_filter_isNegative {M : Type*} [AddCommMonoid M] {n : ℕ}
    (v : Fin n → SuperLetter) (f : Fin n → M) :
    ∑ i ∈ {i | (v i).IsPositive}, f i + ∑ i ∈ {i | (v i).IsNegative}, f i = ∑ i, f i := by
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun i => (v i).IsPositive) f]
  congr 1
  refine Finset.sum_congr (Finset.ext fun i => ?_) fun i _ => rfl
  simp [isNegative_iff_not_isPositive]

/-- Splitting a product over the positions of a super word by the sign of the letter. -/
theorem prod_filter_isPositive_mul_prod_filter_isNegative {M : Type*} [CommMonoid M] {n : ℕ}
    (v : Fin n → SuperLetter) (f : Fin n → M) :
    (∏ i ∈ {i | (v i).IsPositive}, f i) * ∏ i ∈ {i | (v i).IsNegative}, f i = ∏ i, f i := by
  rw [← Finset.prod_filter_mul_prod_filter_not univ (fun i => (v i).IsPositive) f]
  congr 1
  refine Finset.prod_congr (Finset.ext fun i => ?_) fun i _ => rfl
  simp [isNegative_iff_not_isPositive]

/-- **The positive part of the exponent vector of a super word**: the absolute values of its
positive letters, with multiplicity. -/
noncomputable def superPosExp {n : ℕ} (v : Fin n → SuperLetter) : ℕ →₀ ℕ :=
  ∑ i ∈ {i | (v i).IsPositive}, Finsupp.single (v i).absVal 1

/-- **The negative part of the exponent vector of a super word**: the absolute values of its
negative letters, with multiplicity. -/
noncomputable def superNegExp {n : ℕ} (v : Fin n → SuperLetter) : ℕ →₀ ℕ :=
  ∑ i ∈ {i | (v i).IsNegative}, Finsupp.single (v i).absVal 1

variable {n : ℕ}

/-- **The two parts add to the exponent vector of the absolute values**: every position carries
either a positive or a negative letter. -/
theorem superPosExp_add_superNegExp (v : Fin n → SuperLetter) :
    superPosExp v + superNegExp v = wordExponent (superAbs v) := by
  rw [superPosExp, superNegExp, sum_filter_isPositive_add_sum_filter_isNegative, wordExponent]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- The degree of the positive part counts the positive positions. -/
theorem degree_superPosExp (v : Fin n → SuperLetter) :
    (superPosExp v).degree = #{i | (v i).IsPositive} := by
  rw [superPosExp, map_sum]
  simp

/-- The degree of the negative part counts the negative positions. -/
theorem degree_superNegExp (v : Fin n → SuperLetter) :
    (superNegExp v).degree = #{i | (v i).IsNegative} := by
  rw [superNegExp, map_sum]
  simp

/-- **The scalar of `z_v`**: `q` for each positive letter and `-1` for each negative one, so the
product is `q^s(-1)^t` for `s` and `t` the numbers of positive and negative positions. -/
theorem prod_superScalar {K : Type*} [CommRing K] (q : K) (v : Fin n → SuperLetter) :
    ∏ i, superScalar q (v i)
      = q ^ #{i | (v i).IsPositive} * (-1) ^ #{i | (v i).IsNegative} := by
  have hpos : ∏ i ∈ {i | (v i).IsPositive}, superScalar q (v i)
      = q ^ #{i | (v i).IsPositive} := by
    rw [← Finset.prod_const]
    exact Finset.prod_congr rfl fun i hi => superScalar_of_isPositive q (Finset.mem_filter.1 hi).2
  have hneg : ∏ i ∈ {i | (v i).IsNegative}, superScalar q (v i)
      = (-1 : K) ^ #{i | (v i).IsNegative} := by
    rw [← Finset.prod_const]
    exact Finset.prod_congr rfl fun i hi => superScalar_of_isNegative q (Finset.mem_filter.1 hi).2
  rw [← prod_filter_isPositive_mul_prod_filter_isNegative v fun i => superScalar q (v i),
    hpos, hneg]

end ExponentVectors

/-! ### The coded exponent vector of a pair -/

/-- **The coded exponent vector of a pair**: the exponent vector over the codes whose value at the
code `2a` of the positive letter of absolute value `a` is `d₁ a` and whose value at the code
`2a + 1` of the negative one is `d₂ a`. A pair `(d₁, d₂)` of exponent vectors and a multiset of
super letters are the same datum, and this is the translation. -/
noncomputable def superCodeExp (d₁ d₂ : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  Finsupp.mapDomain (fun a => 2 * a) d₁ + Finsupp.mapDomain (fun a => 2 * a + 1) d₂

/-- Doubling is injective. -/
private theorem two_mul_injective : Function.Injective fun a : ℕ => 2 * a := fun x y h => by
  have h' : 2 * x = 2 * y := h
  omega

/-- Doubling and adding one is injective. -/
private theorem two_mul_add_one_injective : Function.Injective fun a : ℕ => 2 * a + 1 :=
  fun x y h => by
    have h' : 2 * x + 1 = 2 * y + 1 := h
    omega

/-- The coded exponent vector at an even code is the first member of the pair. -/
@[simp]
theorem superCodeExp_two_mul (d₁ d₂ : ℕ →₀ ℕ) (a : ℕ) : superCodeExp d₁ d₂ (2 * a) = d₁ a := by
  rw [superCodeExp, Finsupp.add_apply, Finsupp.mapDomain_apply two_mul_injective d₁ a,
    Finsupp.mapDomain_of_notMem_range d₂ (2 * a)
      (by rintro ⟨b, hb⟩; exact absurd (show 2 * b + 1 = 2 * a from hb) (by omega)), add_zero]

/-- The coded exponent vector at an odd code is the second member of the pair. -/
@[simp]
theorem superCodeExp_two_mul_add_one (d₁ d₂ : ℕ →₀ ℕ) (a : ℕ) :
    superCodeExp d₁ d₂ (2 * a + 1) = d₂ a := by
  rw [superCodeExp, Finsupp.add_apply,
    Finsupp.mapDomain_of_notMem_range d₁ (2 * a + 1)
      (by rintro ⟨b, hb⟩; exact absurd (show 2 * b = 2 * a + 1 from hb) (by omega)),
    Finsupp.mapDomain_apply two_mul_add_one_injective d₂ a, zero_add]

/-- **The pair is recovered from its coded exponent vector**: the even codes carry the first member
and the odd codes the second. -/
theorem superCodeExp_inj {d₁ d₂ e₁ e₂ : ℕ →₀ ℕ} (h : superCodeExp d₁ d₂ = superCodeExp e₁ e₂) :
    d₁ = e₁ ∧ d₂ = e₂ := by
  refine ⟨Finsupp.ext fun a => ?_, Finsupp.ext fun a => ?_⟩
  · rw [← superCodeExp_two_mul d₁ d₂ a, ← superCodeExp_two_mul e₁ e₂ a, h]
  · rw [← superCodeExp_two_mul_add_one d₁ d₂ a, ← superCodeExp_two_mul_add_one e₁ e₂ a, h]

/-- The degree of the coded exponent vector is the sum of the two degrees. -/
@[simp]
theorem degree_superCodeExp (d₁ d₂ : ℕ →₀ ℕ) :
    (superCodeExp d₁ d₂).degree = d₁.degree + d₂.degree := by
  rw [superCodeExp, map_add, Finsupp.degree_mapDomain, Finsupp.degree_mapDomain]

/-- **Halving the codes adds the pair**: both `2a` and `2a + 1` halve to `a`, so the absolute
values of the letters the coded vector describes are those of `d₁ + d₂`. -/
theorem mapDomain_div_two_superCodeExp (d₁ d₂ : ℕ →₀ ℕ) :
    Finsupp.mapDomain (fun m => m / 2) (superCodeExp d₁ d₂) = d₁ + d₂ := by
  have h1 : ((fun m => m / 2) ∘ fun a : ℕ => 2 * a) = id :=
    funext fun a => by simp only [Function.comp_apply, id_eq]; omega
  have h2 : ((fun m => m / 2) ∘ fun a : ℕ => 2 * a + 1) = id :=
    funext fun a => by simp only [Function.comp_apply, id_eq]; omega
  rw [superCodeExp, Finsupp.mapDomain_add, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, h1,
    h2, Finsupp.mapDomain_id, Finsupp.mapDomain_id]

/-- **The coded exponent vector of the two parts of a super word is the exponent vector of its
coded word**: a positive letter contributes the even code `2a` and a negative one the odd code
`2a + 1`. -/
theorem superCodeExp_superPosExp_superNegExp {n : ℕ} (v : Fin n → SuperLetter) :
    superCodeExp (superPosExp v) (superNegExp v)
      = wordExponent fun i => superCode (v i) := by
  rw [superCodeExp, superPosExp, superNegExp, Finsupp.mapDomain_finsetSum,
    Finsupp.mapDomain_finsetSum, wordExponent,
    ← sum_filter_isPositive_add_sum_filter_isNegative v
      fun i => Finsupp.single (superCode (v i)) 1]
  congr 1
  · exact Finset.sum_congr rfl fun i hi => by
      rw [Finsupp.mapDomain_single, superCode_of_isPositive (Finset.mem_filter.1 hi).2]
  · exact Finset.sum_congr rfl fun i hi => by
      rw [Finsupp.mapDomain_single, superCode_of_isNegative (Finset.mem_filter.1 hi).2]

/-! ### A super ascending word for the empty step set repeats no negative letter -/

section NoRepeat

variable {n : ℕ}

/-- **A super ascending word for the empty step set repeats no negative letter**: it increases
weakly, so two positions carrying one letter force an adjacent pair carrying it, and
`HJO.Sym.superFundamental` puts such a step of a negative letter in `S`, which is empty here. -/
theorem IsSuperAscendingWord.card_filter_le_one {v : Fin n → SuperLetter}
    (h : IsSuperAscendingWord n ∅ v) {α : SuperLetter} (hα : α.IsNegative) :
    #{i | v i = α} ≤ 1 := by
  have key : ∀ x y : Fin n, x < y → v x = α → v y = α → False := by
    intro x y hxy hx hy
    have hxy' : (x : ℕ) < (y : ℕ) := hxy
    have hy' := y.isLt
    have hyn : (x : ℕ) + 1 < n := by omega
    set l : Fin n := ⟨(x : ℕ) + 1, hyn⟩ with hldef
    have hlval : (l : ℕ) = (x : ℕ) + 1 := by rw [hldef]
    have h1 : α ≤ v l := by
      rw [← hx]
      exact h.monotone (by rw [Fin.le_def, hlval]; omega)
    have h2 : v l ≤ α := by
      rw [← hy]
      exact h.monotone (by rw [Fin.le_def, hlval]; omega)
    have hvl : v l = α := le_antisymm h2 h1
    have hstep := h.mem_of_isNegative x l (by rw [hlval]) (by rw [hx, hvl])
      (by rw [hx]; exact hα)
    exact absurd hstep (Finset.notMem_empty _)
  refine Finset.card_le_one.2 fun a ha b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact (key a b hlt ha hb).elim
  · exact heq
  · exact (key b a hgt hb ha).elim

/-- **The negative part of the exponent vector counts the negative letters**: its entry at `a` is
the number of positions carrying the negative letter of absolute value `a`. -/
theorem superNegExp_apply (v : Fin n → SuperLetter) (a : ℕ) :
    superNegExp v a = #{i | v i = SuperLetter.mk a true} := by
  rw [superNegExp, Finset.sum_apply', Finset.sum_filter, Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hn : (v i).IsNegative
  · have hsign : (ofLex (v i)).2 = true := hn
    have hiff : ((v i).absVal = a) ↔ (v i = SuperLetter.mk a true) :=
      ⟨fun hc => SuperLetter.ext (by rw [hc, SuperLetter.absVal_mk])
        (by rw [hsign, SuperLetter.sign_mk]), fun hc => by rw [hc, SuperLetter.absVal_mk]⟩
    rw [ite_eq_left hn, Finsupp.single_apply]
    exact if_congr hiff rfl rfl
  · have hsign : (ofLex (v i)).2 = false := (SuperLetter.isPositive_iff_not_isNegative _).2 hn
    have hne : ¬(v i = SuperLetter.mk a true) := fun hc => by
      rw [hc, SuperLetter.sign_mk] at hsign
      exact absurd hsign (by simp)
    rw [ite_eq_right hn, ite_eq_right hne]

/-- **At the empty step set the negative part of the exponent vector is squarefree**: no negative
letter is repeated. -/
theorem superNegExp_apply_le_one {v : Fin n → SuperLetter} (h : IsSuperAscendingWord n ∅ v)
    (a : ℕ) : superNegExp v a ≤ 1 := by
  rw [superNegExp_apply]
  exact h.card_filter_le_one (SuperLetter.sign_mk a true)

end NoRepeat

/-! ### The super word of a pair of exponent vectors -/

section WordOfPair

/-- **The super word of a pair of exponent vectors**: the weakly increasing word over the alphabet
whose positive letters carry the absolute values of `d₁` and whose negative letters carry those of
`d₂`. It is the sorted word of the coded exponent vector `HJO.Sym.superCodeExp`, decoded — which is
how the sorting of words over `ℕ` serves the alphabet. -/
noncomputable def superWordOfPair (n : ℕ) (d₁ d₂ : ℕ →₀ ℕ) : Fin n → SuperLetter :=
  fun k => superDecode (wordOfExponent n (superCodeExp d₁ d₂) k)

variable {n : ℕ} {d₁ d₂ : ℕ →₀ ℕ}

/-- The coded word of the super word of a pair is the sorted word of the coded exponent vector. -/
theorem superCode_superWordOfPair :
    (fun k => superCode (superWordOfPair n d₁ d₂ k)) = wordOfExponent n (superCodeExp d₁ d₂) :=
  funext fun _ => superCode_superDecode _

/-- The coded exponent vector of a pair of total degree `n` has `n` letters. -/
theorem card_toMultiset_superCodeExp (hd : d₁.degree + d₂.degree = n) :
    Multiset.card (Finsupp.toMultiset (superCodeExp d₁ d₂)) = n := by
  rw [card_toMultiset_eq_degree, degree_superCodeExp, hd]

/-- The super word of a pair increases weakly: decoding is increasing and the sorted word is. -/
theorem monotone_superWordOfPair (hd : d₁.degree + d₂.degree = n) :
    Monotone (superWordOfPair n d₁ d₂) :=
  superDecode_monotone.comp (monotone_wordOfExponent (card_toMultiset_superCodeExp hd))

/-- The exponent vector of the coded word of the super word of a pair is the coded exponent
vector. -/
theorem wordExponent_superCode_superWordOfPair (hd : d₁.degree + d₂.degree = n) :
    wordExponent (fun k => superCode (superWordOfPair n d₁ d₂ k)) = superCodeExp d₁ d₂ := by
  rw [superCode_superWordOfPair]
  exact wordExponent_wordOfExponent (card_toMultiset_superCodeExp hd)

/-- **The absolute values of the super word of a pair have exponent vector `d₁ + d₂`**: halving the
codes adds the pair. -/
theorem wordExponent_superAbs_superWordOfPair (hd : d₁.degree + d₂.degree = n) :
    wordExponent (superAbs (superWordOfPair n d₁ d₂)) = d₁ + d₂ := by
  have habs : superAbs (superWordOfPair n d₁ d₂)
      = fun k => superCode (superWordOfPair n d₁ d₂ k) / 2 :=
    funext fun k => absVal_eq_superCode_div_two _
  rw [habs, wordExponent_map (fun m => m / 2) fun k => superCode (superWordOfPair n d₁ d₂ k),
    wordExponent_superCode_superWordOfPair hd, mapDomain_div_two_superCodeExp]

/-- **The two parts of the exponent vector of the super word of a pair are the pair**: both are
read off the coded exponent vector, which determines them. -/
theorem superPosExp_superWordOfPair (hd : d₁.degree + d₂.degree = n) :
    superPosExp (superWordOfPair n d₁ d₂) = d₁ ∧ superNegExp (superWordOfPair n d₁ d₂) = d₂ :=
  superCodeExp_inj (by
    rw [superCodeExp_superPosExp_superNegExp, wordExponent_superCode_superWordOfPair hd])

/-- **The super word of a pair whose second member is squarefree is a super ascending word for the
empty step set**: it increases weakly by construction, and a repeated negative letter would make an
odd entry of the coded exponent vector at least `2`, whereas that entry is `d₂ a ≤ 1`. -/
theorem isSuperAscendingWord_superWordOfPair (hd : d₁.degree + d₂.degree = n)
    (h2 : ∀ a, d₂ a ≤ 1) : IsSuperAscendingWord n ∅ (superWordOfPair n d₁ d₂) := by
  refine ⟨fun k l hkl => monotone_superWordOfPair hd (by rw [Fin.le_def]; omega),
    fun _ _ _ _ _ => Finset.notMem_empty _, fun k l hkl heq hneg => ?_⟩
  exfalso
  have hwkl : superCode (superWordOfPair n d₁ d₂ k) = superCode (superWordOfPair n d₁ d₂ l) :=
    congrArg superCode heq
  have hkne : k ≠ l := fun hc => by rw [hc] at hkl; omega
  have hcard : 1 < #{i | superCode (superWordOfPair n d₁ d₂ i)
      = superCode (superWordOfPair n d₁ d₂ k)} :=
    Finset.one_lt_card.2 ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩, l,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hwkl.symm⟩, hkne⟩
  have hval : superCode (superWordOfPair n d₁ d₂ k)
      = 2 * (superWordOfPair n d₁ d₂ k).absVal + 1 := superCode_of_isNegative hneg
  have hexp := wordExponent_apply (fun i => superCode (superWordOfPair n d₁ d₂ i))
    (superCode (superWordOfPair n d₁ d₂ k))
  rw [wordExponent_superCode_superWordOfPair hd] at hexp
  have hle := h2 (superWordOfPair n d₁ d₂ k).absVal
  rw [← superCodeExp_two_mul_add_one d₁ d₂, ← hval] at hle
  omega

end WordOfPair

/-! ### The bijection between super ascending words and squarefree splittings -/

/-- **A squarefree exponent vector**: no letter occurs twice in the word it describes, which is the
condition on the exponent vector of a strictly increasing word. Quantified over the support so as to
be decidable; `HJO.Sym.isSquarefreeExp_iff` reads it at every letter. -/
def IsSquarefreeExp (d : ℕ →₀ ℕ) : Prop := ∀ a ∈ d.support, d a ≤ 1

/-- Squarefreeness is decidable: it is a bounded quantification over the support. -/
instance instDecidableIsSquarefreeExp (d : ℕ →₀ ℕ) : Decidable (IsSquarefreeExp d) := by
  unfold IsSquarefreeExp; infer_instance

/-- Squarefreeness read at every letter: outside the support the entry is `0`. -/
theorem isSquarefreeExp_iff {d : ℕ →₀ ℕ} : IsSquarefreeExp d ↔ ∀ a, d a ≤ 1 := by
  refine ⟨fun h a => ?_, fun h a _ => h a⟩
  by_cases ha : a ∈ d.support
  · exact h a ha
  · rw [Finsupp.notMem_support_iff.1 ha]
    omega


/-- **The super words contributing to one monomial of `F̃_{n,∅}`**: the super ascending words of
length `n` for the empty step set whose absolute values have exponent vector `d`. Every letter has
its absolute value in the support of `d`, which is what makes them a `Finset`. -/
noncomputable def superRowWords (n : ℕ) (d : ℕ →₀ ℕ) : Finset (Fin n → SuperLetter) :=
  {v ∈ Fintype.piFinset fun _ : Fin n => letterFinset d.support |
    IsSuperAscendingWord n ∅ v ∧ wordExponent (superAbs v) = d}

/-- **Membership in the contributing words**: the bound on the letters is carried by the exponent
vector, so only the two stated conditions are content. -/
theorem mem_superRowWords {n : ℕ} {d : ℕ →₀ ℕ} {v : Fin n → SuperLetter} :
    v ∈ superRowWords n d ↔ IsSuperAscendingWord n ∅ v ∧ wordExponent (superAbs v) = d := by
  rw [superRowWords, Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h => h.2, fun h => ⟨fun i => ?_, h⟩⟩
  rw [mem_letterFinset, ← h.2]
  exact (mem_support_wordExponent (superAbs v) ((v i).absVal)).2 ⟨i, rfl⟩

/-- **The squarefree splittings of an exponent vector**: the pairs `(d₁, d₂)` with `d₁ + d₂ = d` no
entry of whose second member exceeds `1`. These index the quadruples `(s, t, u, w)`:
`d₁` is the exponent vector of the weakly increasing `u` and `d₂` that of the strictly increasing
`w`. -/
noncomputable def superSplits (d : ℕ →₀ ℕ) : Finset ((ℕ →₀ ℕ) × (ℕ →₀ ℕ)) :=
  {p ∈ Finset.antidiagonal d | IsSquarefreeExp p.2}

/-- **Membership in the squarefree splittings**, with the bound stated at every letter: outside the
support the entry is `0`. -/
theorem mem_superSplits {d : ℕ →₀ ℕ} {p : (ℕ →₀ ℕ) × (ℕ →₀ ℕ)} :
    p ∈ superSplits d ↔ p.1 + p.2 = d ∧ ∀ a, p.2 a ≤ 1 := by
  rw [superSplits, Finset.mem_filter, Finset.mem_antidiagonal]
  exact and_congr_right fun _ => isSquarefreeExp_iff

/-- **The bijection of `HJO.ParkingFunctions.realisation_thetaLambda_completeHomog`**: a super
ascending word for the empty step set is sent to the pair of exponent vectors of the absolute values
of its positive and of its negative letters, and that is a bijection onto the squarefree splittings
carrying `z_v` to `q^s(-1)^t`.

Injectivity is that a weakly increasing word is determined by its multiset of letters
(`HJO.Sym.eq_of_wordExponent_eq`, read through `HJO.Sym.superCode`), and surjectivity is
`HJO.Sym.superWordOfPair`. -/
theorem sum_prod_superScalar_eq_sum_superSplits {K : Type*} [CommRing K] (q : K) {n : ℕ}
    {d : ℕ →₀ ℕ} (hd : d.degree = n) :
    ∑ v ∈ superRowWords n d, ∏ i, superScalar q (v i)
      = ∑ p ∈ superSplits d, q ^ p.1.degree * (-1) ^ p.2.degree := by
  refine Finset.sum_bij (fun v _ => (superPosExp v, superNegExp v)) (fun v hv => ?_)
    (fun v hv v' hv' h => ?_) (fun p hp => ?_) fun v _ => ?_
  · rw [mem_superRowWords] at hv
    rw [mem_superSplits]
    exact ⟨(superPosExp_add_superNegExp v).trans hv.2, superNegExp_apply_le_one hv.1⟩
  · rw [mem_superRowWords] at hv hv'
    simp only [Prod.mk.injEq] at h
    have hcode : wordExponent (fun i => superCode (v i))
        = wordExponent fun i => superCode (v' i) := by
      rw [← superCodeExp_superPosExp_superNegExp, ← superCodeExp_superPosExp_superNegExp, h.1, h.2]
    have heq := eq_of_monotone_of_wordExponent_eq
      (fun i j hij => superCode_strictMono.monotone (hv.1.monotone hij))
      (fun i j hij => superCode_strictMono.monotone (hv'.1.monotone hij)) hcode
    exact funext fun i => superCode_injective (congrFun heq i)
  · rw [mem_superSplits] at hp
    have hdeg : p.1.degree + p.2.degree = n := by
      have hadd := map_add (Finsupp.degree : (ℕ →₀ ℕ) →+ ℕ) p.1 p.2
      rw [hp.1, hd] at hadd
      omega
    refine ⟨superWordOfPair n p.1 p.2, ?_, ?_⟩
    · rw [mem_superRowWords]
      exact ⟨isSuperAscendingWord_superWordOfPair hdeg hp.2,
        (wordExponent_superAbs_superWordOfPair hdeg).trans hp.1⟩
    · obtain ⟨hp1, hp2⟩ := superPosExp_superWordOfPair hdeg
      rw [hp1, hp2]
  · rw [prod_superScalar, degree_superPosExp, degree_superNegExp]

/-! ### Words of a prescribed exponent vector -/

section PrescribedExponent

variable {n : ℕ}

/-- **A word with a strict step everywhere is injective**, so no letter is repeated in it: its
exponent vector takes only the values `0` and `1`. -/
theorem wordExponent_apply_le_one {w : Fin n → ℕ} (hw : IsAscendingWord n (Ico 1 n) w) (a : ℕ) :
    wordExponent w a ≤ 1 := by
  have hsm : StrictMono w := by
    cases n with
    | zero => exact fun x => x.elim0
    | succ N =>
      refine Fin.strictMono_iff_lt_succ.2 fun i => hw.lt_of_mem _ _ (by simp) ?_
      simp only [Fin.val_succ, mem_Ico]
      omega
  rw [wordExponent_apply]
  refine Finset.card_le_one.2 fun x hx y hy => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  exact hsm.injective (hx.trans hy.symm)

/-- **The word of a squarefree exponent vector increases strictly at every step**: a repetition
would make an entry of the vector at least `2`. -/
theorem isAscendingWord_wordOfExponent {d : ℕ →₀ ℕ}
    (hcard : Multiset.card (Finsupp.toMultiset d) = n) (h1 : ∀ a, d a ≤ 1) :
    IsAscendingWord n (Ico 1 n) (wordOfExponent n d) := by
  refine ⟨monotone_wordOfExponent hcard, fun k l hkl _ => ?_⟩
  rcases lt_or_eq_of_le (monotone_wordOfExponent hcard
    (show k ≤ l from by rw [Fin.le_def]; omega)) with h | h
  · exact h
  · exfalso
    have hkne : k ≠ l := fun hc => by rw [hc] at hkl; omega
    have hcard2 : 1 < #{i | wordOfExponent n d i = wordOfExponent n d k} :=
      Finset.one_lt_card.2 ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩, l,
        Finset.mem_filter.2 ⟨Finset.mem_univ _, h.symm⟩, hkne⟩
    have hexp := wordExponent_apply (wordOfExponent n d) (wordOfExponent n d k)
    rw [wordExponent_wordOfExponent hcard] at hexp
    have := h1 (wordOfExponent n d k)
    omega

end PrescribedExponent

/-! ### A coefficient of the super fundamental of a single row -/

/-- The contributing words are among the tuples of letters of bounded absolute value. -/
theorem superRowWords_subset (n : ℕ) (d : ℕ →₀ ℕ) :
    superRowWords n d ⊆ Fintype.piFinset fun _ : Fin n => letterFinset d.support := by
  rw [superRowWords]
  exact Finset.filter_subset _ _

/-- **`z_v` is one monomial**: the exponent vector of the absolute values, with the product of the
scalars for its coefficient. -/
theorem superMonomial_eq_monomial {K : Type*} [CommRing K] (q : K) {n : ℕ}
    (v : Fin n → SuperLetter) :
    superMonomial K q v
      = MvPowerSeries.monomial (wordExponent (superAbs v)) (∏ i, superScalar q (v i)) := by
  rw [superMonomial, prod_superVar, wordExponent]
  simp only [superAbs_apply]

/-- **A coefficient of `F̃_{n,∅}`**: the signed count `∑_v q^s(-1)^t` over the super ascending words
for the empty step set whose absolute values have the given exponent vector. -/
theorem coeff_superFundamental_empty {K : Type*} [CommRing K] (q : K) (n : ℕ) (d : ℕ →₀ ℕ) :
    MvPowerSeries.coeff d (superFundamental K q n ∅)
      = ∑ v ∈ superRowWords n d, ∏ i, superScalar q (v i) := by
  have hcoeff : ∀ v : Fin n → SuperLetter,
      MvPowerSeries.coeff d (if IsSuperAscendingWord n ∅ v then superMonomial K q v else 0)
        = if v ∈ superRowWords n d then ∏ i, superScalar q (v i) else 0 := by
    intro v
    by_cases hasc : IsSuperAscendingWord n ∅ v
    · rw [ite_eq_left hasc, superMonomial_eq_monomial, MvPowerSeries.coeff_monomial]
      by_cases hexp : wordExponent (superAbs v) = d
      · rw [ite_eq_left hexp.symm, ite_eq_left (mem_superRowWords.2 ⟨hasc, hexp⟩)]
      · rw [ite_eq_right fun hc => hexp hc.symm,
          ite_eq_right fun hc => hexp (mem_superRowWords.1 hc).2]
    · rw [ite_eq_right hasc, map_zero, ite_eq_right fun hc => hasc (mem_superRowWords.1 hc).1]
  have hs : ∀ v : Fin n → SuperLetter,
      MvPowerSeries.coeff d (if IsSuperAscendingWord n ∅ v then superMonomial K q v else 0) ≠ 0 →
        v ∈ Fintype.piFinset fun _ : Fin n => letterFinset d.support := by
    intro v hv
    rw [hcoeff v] at hv
    by_cases hmem : v ∈ superRowWords n d
    · exact superRowWords_subset n d hmem
    · exact absurd (ite_eq_right hmem) hv
  rw [coeff_superFundamental_eq_sum q n ∅ hs, Finset.sum_congr rfl fun v _ => hcoeff v,
    Finset.sum_ite_mem, Finset.inter_eq_right.2 (superRowWords_subset n d)]

end HJO.Sym

namespace HJO.ParkingFunctions

open HJO.Sym

/-! ### The coefficients of the two fundamentals of a single row -/

section GesselCoeff

variable {K : Type*} [CommRing K]

/-- **A coefficient of `F_{n,∅}` is the indicator of total degree `n`**: the exponent vectors of the
weakly increasing words of length `n` are exactly those of total degree `n`. -/
theorem coeff_gessel_empty (n : ℕ) (d : ℕ →₀ ℕ) :
    MvPowerSeries.coeff d (gessel K n ∅) = if d.degree = n then 1 else 0 := by
  by_cases hdeg : d.degree = n
  · have hcard : Multiset.card (Finsupp.toMultiset d) = n := by
      rw [card_toMultiset_eq_degree, hdeg]
    have hasc : IsAscendingWord n ∅ (wordOfExponent n d) :=
      ⟨monotone_wordOfExponent hcard, fun _ _ _ h => absurd h (Finset.notMem_empty _)⟩
    have h := coeff_wordExponent_gessel K (Finset.empty_subset (Ico 1 n)) hasc
    rw [wordExponent_wordOfExponent hcard] at h
    rw [ite_eq_left hdeg]
    exact h
  · rw [ite_eq_right hdeg]
    refine coeff_gessel_eq_zero_of_forall_ne K fun w hw hdw => hdeg ?_
    rw [hdw, degree_wordExponent]

/-- **A coefficient of `F_{n,\{1,…,n-1\}}` is the indicator of the squarefree exponent vectors of
total degree `n`**: those are the exponent vectors of the strictly increasing words of length
`n`. -/
theorem coeff_gessel_Ico (n : ℕ) (d : ℕ →₀ ℕ) :
    MvPowerSeries.coeff d (gessel K n (Ico 1 n))
      = if d.degree = n ∧ IsSquarefreeExp d then 1 else 0 := by
  by_cases hd : d.degree = n ∧ IsSquarefreeExp d
  · have hcard : Multiset.card (Finsupp.toMultiset d) = n := by
      rw [card_toMultiset_eq_degree, hd.1]
    have h := coeff_wordExponent_gessel K Subset.rfl
      (isAscendingWord_wordOfExponent hcard (isSquarefreeExp_iff.1 hd.2))
    rw [wordExponent_wordOfExponent hcard] at h
    rw [ite_eq_left hd]
    exact h
  · rw [ite_eq_right hd]
    refine coeff_gessel_eq_zero_of_forall_ne K fun w hw hdw =>
      hd ⟨?_, isSquarefreeExp_iff.2 fun a => ?_⟩
    · rw [hdw, degree_wordExponent]
    · rw [hdw]
      exact wordExponent_apply_le_one hw a

end GesselCoeff


/-! ### The signed sum of the row products is the super fundamental of a row -/

/-- **The identity underlying `HJO.ParkingFunctions.realisation_thetaLambda_completeHomog`**, with
no realisation left in it: `∑_{s+t=r}q^s(-1)^tF_{s,∅}F_{t,\{1,…,t-1\}} = F̃_{r,∅}`.

Both sides are read coefficientwise at an exponent vector `d`. A coefficient of the left side counts
the splittings `d = d₁ + d₂` with `d₂` squarefree, weighted by `q^{|d₁|}(-1)^{|d₂|}`, the inner sum
over `j` having the single surviving term `j = |d₁|`; a coefficient of the right side is the signed
count of the super ascending words of exponent vector `d`, and
`HJO.Sym.sum_prod_superScalar_eq_sum_superSplits` is the bijection between the two. -/
theorem sum_gessel_eq_superFundamental {K : Type*} [CommRing K] (q : K) (r : ℕ) :
    ∑ j ∈ range (r + 1), (MvPowerSeries.C q : AlphabetSeries K) ^ j * (-1) ^ (r - j) *
        (gessel K j ∅ * gessel K (r - j) (Ico 1 (r - j)))
      = superFundamental K q r ∅ := by
  refine MvPowerSeries.ext fun d => ?_
  rw [map_sum, coeff_superFundamental_empty]
  have hterm : ∀ j : ℕ, MvPowerSeries.coeff d ((MvPowerSeries.C q : AlphabetSeries K) ^ j *
      (-1) ^ (r - j) * (gessel K j ∅ * gessel K (r - j) (Ico 1 (r - j))))
        = ∑ p ∈ Finset.antidiagonal d, q ^ j * (-1) ^ (r - j) *
            ((if p.1.degree = j then (1 : K) else 0) *
              (if p.2.degree = r - j ∧ IsSquarefreeExp p.2 then 1 else 0)) := by
    intro j
    rw [show ((MvPowerSeries.C q : AlphabetSeries K) ^ j * (-1) ^ (r - j))
          = MvPowerSeries.C (q ^ j * (-1) ^ (r - j)) by
        rw [map_mul, map_pow, map_pow, map_neg, map_one],
      MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by rw [coeff_gessel_empty, coeff_gessel_Ico]
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_comm]
  by_cases hdr : d.degree = r
  · rw [sum_prod_superScalar_eq_sum_superSplits q hdr, superSplits, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    have hpdeg : p.1.degree + p.2.degree = r := by
      have hadd := map_add (Finsupp.degree : (ℕ →₀ ℕ) →+ ℕ) p.1 p.2
      rw [hp, hdr] at hadd
      omega
    have hzero : ∀ j ∈ range (r + 1), j ≠ p.1.degree →
        q ^ j * (-1) ^ (r - j) * ((if p.1.degree = j then (1 : K) else 0) *
          (if p.2.degree = r - j ∧ IsSquarefreeExp p.2 then 1 else 0)) = 0 := by
      intro j _ hne
      rw [ite_eq_right fun hc => hne hc.symm, zero_mul, mul_zero]
    rw [Finset.sum_eq_single_of_mem _ (mem_range.2 (show p.1.degree < r + 1 by omega)) hzero,
      ite_eq_left rfl, one_mul, show r - p.1.degree = p.2.degree from by omega]
    by_cases hsq : IsSquarefreeExp p.2
    · rw [ite_eq_left ⟨rfl, hsq⟩, ite_eq_left hsq, mul_one]
    · rw [ite_eq_right fun hc => hsq hc.2, ite_eq_right hsq, mul_zero]
  · have hempty : superRowWords r d = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro v hv
      rw [mem_superRowWords] at hv
      exact hdr (by rw [← hv.2, degree_wordExponent])
    rw [hempty, Finset.sum_empty]
    refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_antidiagonal] at hp
    by_cases h1 : p.1.degree = j
    · by_cases h2 : p.2.degree = r - j ∧ IsSquarefreeExp p.2
      · exfalso
        have hjr : j ≤ r := by rw [mem_range] at hj; omega
        have hadd := map_add (Finsupp.degree : (ℕ →₀ ℕ) →+ ℕ) p.1 p.2
        rw [hp] at hadd
        exact hdr (by rw [hadd, h1, h2.1]; omega)
      · rw [ite_eq_right h2, mul_zero, mul_zero]
    · rw [ite_eq_right h1, zero_mul, mul_zero]


/-! ### The plethysm of a complete homogeneous function -/

/-- **The plethysm of a complete homogeneous function is a super
fundamental.** `ι(θ₀(h_r)) = F̃_{r,∅}` for every realisation `ι`.

`θ₀(h_r) = ∑_{s+t=r}q^s(-1)^th_se_t` is `HJO.Sweep.theta_completeHomog`, read on `Λ` as
`HJO.Sym.thetaLambda_completeHomog` (`HJO.Sweep.theta_C` identifies `thetaLambda` with the
restriction of `HJO.Sweep.theta` to `V_0`); `ι` is an algebra map, so the factors become `F_{s,∅}`
and `F_{t,\{1,…,t-1\}}` by `HJO.ParkingFunctions.realisation_completeHomog` and
`HJO.ParkingFunctions.realisation_elemSymm` — at `s = 0` and `t = 0` alike, those two lemmas being
stated without a positivity hypothesis. The remaining identity is
`HJO.ParkingFunctions.sum_gessel_eq_superFundamental`, the bijection between the super ascending
words for the empty step set and the quadruples `(s, t, u, w)`.

The hypothesis `r ≥ 1` is not needed: at `r = 0` both sides are `1`, the empty word being the only
super word of length `0`. -/
@[hjo "lem_om_theta_hsymm_super_row"]
theorem realisation_thetaLambda_completeHomog {K : Type*} [CommRing K] [Algebra ℚ K]
    {ι : Lambda K →ₐ[K] AlphabetSeries K} (hι : IsRealisation ι) (q : K) (r : ℕ) :
    ι (thetaLambda q (completeHomog K r)) = superFundamental K q r ∅ := by
  have hC : ι (MvPolynomial.C q) = (MvPowerSeries.C q : AlphabetSeries K) := by
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, MvPowerSeries.algebraMap_apply]
    simp
  rw [thetaLambda_completeHomog, map_sum, ← sum_gessel_eq_superFundamental q r]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_neg, map_one, hC,
    realisation_completeHomog hι, realisation_elemSymm hι]

end HJO.ParkingFunctions
