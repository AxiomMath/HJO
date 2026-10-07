/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.SuperStd
public import HJO.CarlssonMellit.SuperSchur
public meta import HJO.Attr

/-! # The sum over the signs of a super word factorises

The expansion of the characteristic series over the super alphabet is grouped by absolute values:
the super words `v ∈ 𝒜^n` with a prescribed word `|v| = u` of absolute values form a block of `2^n`
words, one for each tuple of signs, and this file evaluates the block sum
`∑_{|v| = u}q^{inv^±(R,v)}z_v`. It factorises completely: the monomial `x_u` and the plain
inversion weight `q^{inv(R,u)}` are common to the block, and each position contributes
independently the two signs it may carry, so the block sum is
`q^{inv(R,u)}x_u∏_i(q - q^{d_i(R,u)})` with `d_i(R,u)` the equal-partner count at the position.

## Main definitions

* `HJO.Sym.superWord`: the super word with prescribed absolute values and signs.
* `HJO.Sym.superFibre`: the block `{v ∈ 𝒜^n : |v| = u}`.
* `HJO.Sym.signFactor`: the factor `c_i(v)` one position contributes, `q` at a positive sign and
  `-q^{d}` at a negative one.

## Main results

* `HJO.Sym.superFibre_eq_image`: the block is indexed by the sign tuples, which is the bijection
  `{v ∈ 𝒜^n : |v| = u} ≃ \{1, -1\}^n` the proof of the factorisation opens with.
* `HJO.Sym.superMonomial_eq_smul_wordMonomial`: `z_v = x_{|v|}∏_i s_i`.
* `HJO.Dyck.sum_pow_superInvNumber_smul_superMonomial`: the block sum factorises,
  `∑_{|v| = u}q^{inv^±(R,v)}z_v = q^{inv(R,u)}x_u∏_i(q - q^{d_i(R,u)})`.

## Implementation notes

*The block is a `Finset` of super words, not a subtype.* `HJO.Sym.superFibre` is the set of super
words with letters of the prescribed absolute values, filtered by `|v| = u`; the letters of bounded
absolute value are finite by `HJO.Sym.letterFinset`, so the filter of that finite set is
`{v ∈ 𝒜^n : |v| = u}` with a carrier of finiteness attached and nothing else —
`HJO.Sym.mem_superFibre` says membership is exactly `|v| = u`. The bijection onto the sign tuples is
then the lemma `HJO.Sym.superFibre_eq_image`, and it is what turns the block sum into a sum over
`Fin n → Bool`, where `Finset.sum_prod_piFinset` expands the product of `n` binomials.

*Two customary hypotheses are dropped.* Neither the requirement that the pairs of `R` increase nor
the positivity of the entries of `u` is used: the only input about `R` is
`HJO.Dyck.superInvNumber_eq_invNumber_add_sum_equalPartners`, which is itself stated for an
arbitrary `R`, and absolute values are indexed from `0` throughout this library, so positivity is
vacuous. The statement here is therefore the factorisation at an arbitrary `R` and an arbitrary `u`.

The sign of a letter is a `Bool`, `true` reading as a negative letter, of sign `ε = -1`, so a sign
tuple is a function `Fin n → Bool` and the two-element sum over one position is `Fintype.sum_bool`.
The scalar `q` and the inversion weights live in the base ring `K`, the monomials in
`HJO.Sym.AlphabetSeries K`, and the weight acts on the monomial by `•`, exactly as in
`HJO.Dyck.coeff_charSeries_eq_coeff_sum_wordMonomial`.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 3, for the super alphabet and the sum over the signs of a super word behind the
lemma `HJO.Dyck.sum_pow_superInvNumber_smul_superMonomial`.
-/

@[expose] public section

open Finset

namespace HJO.Sym

variable {n : ℕ}

/-! ### The super words of a prescribed absolute value -/

/-- **The super word with prescribed absolute values `u` and signs `ε`**: the letter at the position
`i` is the one of absolute value `u_i` whose sign is `ε_i`, the sign `false` reading as positive.
Ranging over the sign tuples, this enumerates the super words `v` with `|v| = u`. -/
def superWord (u : Fin n → ℕ) (ε : Fin n → Bool) : Fin n → SuperLetter :=
  fun i => SuperLetter.mk (u i) (ε i)

/-- The absolute values of the prescribed word are the prescribed ones. -/
@[simp]
theorem superAbs_superWord (u : Fin n → ℕ) (ε : Fin n → Bool) : superAbs (superWord u ε) = u :=
  rfl

/-- The sign the prescribed word carries at a position is the prescribed one. -/
@[simp]
theorem sign_superWord (u : Fin n → ℕ) (ε : Fin n → Bool) (i : Fin n) :
    (ofLex (superWord u ε i)).2 = ε i :=
  rfl

/-- Distinct sign tuples give distinct super words: the signs are read back off the letters. -/
theorem superWord_injective (u : Fin n → ℕ) : Function.Injective (superWord u) := fun ε ε' h =>
  funext fun i => by rw [← sign_superWord u ε i, ← sign_superWord u ε' i, congrFun h i]

/-- Every super word is the prescribed word of its own absolute values and signs, which with
`HJO.Sym.superWord_injective` is the bijection the proof of the factorisation opens with. -/
theorem superWord_superAbs (v : Fin n → SuperLetter) :
    superWord (superAbs v) (fun i => (ofLex (v i)).2) = v :=
  funext fun _ => SuperLetter.ext rfl rfl

/-- **The block `{v ∈ 𝒜^n : |v| = u}`** of super words with the prescribed absolute values: the
words with letters of those absolute values, of which there are finitely many by
`HJO.Sym.letterFinset`, filtered by `|v| = u`. The filter is the whole condition — see
`HJO.Sym.mem_superFibre` — the enclosing set being only what makes the block a `Finset`. -/
def superFibre (u : Fin n → ℕ) : Finset (Fin n → SuperLetter) :=
  {v ∈ Fintype.piFinset fun i => letterFinset {u i} | superAbs v = u}

/-- A super word belongs to the block of `u` exactly when its absolute values are `u`. -/
@[simp]
theorem mem_superFibre {u : Fin n → ℕ} {v : Fin n → SuperLetter} :
    v ∈ superFibre u ↔ superAbs v = u := by
  refine ⟨fun h => (mem_filter.1 h).2,
    fun h => mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => ?_, h⟩⟩
  rw [mem_letterFinset, mem_singleton, ← superAbs_apply, h]

/-- **The block of `u` is indexed by the sign tuples**: it is the image of `Fin n → Bool` under
`HJO.Sym.superWord`, which is the bijection from `{v ∈ 𝒜^n : |v| = u}` onto
`{1, -1}^n` and is what makes the block sum a sum of `2^n` terms. -/
theorem superFibre_eq_image (u : Fin n → ℕ) : superFibre u = univ.image (superWord u) := by
  ext v
  rw [mem_superFibre, mem_image]
  refine ⟨fun h => ⟨fun i => (ofLex (v i)).2, mem_univ _, ?_⟩, ?_⟩
  · rw [← h]
    exact superWord_superAbs v
  · rintro ⟨ε, -, rfl⟩
    exact superAbs_superWord u ε

/-! ### The monomial of a super word, and the factor a sign contributes -/

variable {K : Type*} [CommRing K]

/-- **The monomial of a super word is a scalar multiple of the monomial of its absolute values**:
`z_v = x_{|v|}∏_i s_i`, the scalar being `q` at each positive letter and `-1` at each negative one.
This is the step of the proof of the factorisation that pulls the variables out of `z_v`. -/
theorem superMonomial_eq_smul_wordMonomial (q : K) (v : Fin n → SuperLetter) :
    superMonomial K q v = (∏ i, superScalar q (v i)) • wordMonomial K (superAbs v) := by
  rw [superMonomial, prod_superVar, wordMonomial_eq_monomial, ← map_smul, smul_eq_mul, mul_one]
  rfl

/-- The scalar of the prescribed word at a position is read off the prescribed sign. -/
@[simp]
theorem superScalar_superWord (q : K) (u : Fin n → ℕ) (ε : Fin n → Bool) (i : Fin n) :
    superScalar q (superWord u ε i) = cond (ε i) (-1) q :=
  rfl

/-- **The factor `c_i(v)` one position contributes** to the block sum: `q` when the letter at the
position is positive, and `-q^{d}` when it is negative, `d` being the equal-partner count there.
It absorbs both the sign of the monomial and the inversions the negative letter creates. -/
def signFactor (q : K) (d : ℕ) (b : Bool) : K :=
  cond b (-q ^ d) q

/-- A positive sign contributes `q`. -/
@[simp]
theorem signFactor_false (q : K) (d : ℕ) : signFactor q d false = q :=
  rfl

/-- A negative sign contributes `-q^{d}`. -/
@[simp]
theorem signFactor_true (q : K) (d : ℕ) : signFactor q d true = -q ^ d :=
  rfl

/-- **The two signs at one position contribute `q - q^{d}`**: this is the binomial the product of
the statement is a product of. -/
theorem sum_signFactor (q : K) (d : ℕ) : ∑ b : Bool, signFactor q d b = q - q ^ d := by
  rw [Fintype.sum_bool, signFactor_true, signFactor_false]
  ring

end HJO.Sym

namespace HJO.Dyck

open HJO.Sym

variable {n : ℕ} {K : Type*} [CommRing K]

/-- **The inversion weight of a prescribed word splits over the positions**:
`q^{inv^±(R,v)} = q^{inv(R,u)}∏_{i : v_i negative}q^{d_i(R,u)}`, the second factor written as a
product over all positions with a positive sign contributing `1`. This is
`HJO.Dyck.superInvNumber_eq_invNumber_add_sum_equalPartners` read multiplicatively. -/
theorem pow_superInvNumber_superWord (q : K) (R : Finset (Fin n × Fin n)) (u : Fin n → ℕ)
    (ε : Fin n → Bool) :
    q ^ superInvNumber R (superWord u ε)
      = q ^ invNumber R u * ∏ i, cond (ε i) (q ^ equalPartners R u i) 1 := by
  rw [superInvNumber_eq_invNumber_add_sum_equalPartners, superAbs_superWord, pow_add,
    ← Finset.prod_pow_eq_pow_sum, Finset.prod_filter]
  refine congrArg _ (Finset.prod_congr rfl fun i _ => ?_)
  rw [Bool.cond_eq_ite]
  exact if_congr Iff.rfl rfl rfl

/-- **The term of the block sum at a prescribed word**:
`q^{inv^±(R,v)}z_v = q^{inv(R,u)}x_u∏_i c_i(v)`, with `c_i(v)` the factor
`HJO.Sym.signFactor` of the sign at the position. Both the monomial and the inversion weight have
been pulled apart over the positions, and the two contributions at one position have been
multiplied together. -/
theorem pow_superInvNumber_smul_superMonomial_superWord (q : K) (R : Finset (Fin n × Fin n))
    (u : Fin n → ℕ) (ε : Fin n → Bool) :
    q ^ superInvNumber R (superWord u ε) • superMonomial K q (superWord u ε)
      = (q ^ invNumber R u * ∏ i, signFactor q (equalPartners R u i) (ε i)) • wordMonomial K u := by
  rw [pow_superInvNumber_superWord, superMonomial_eq_smul_wordMonomial, superAbs_superWord,
    smul_smul, mul_assoc, ← Finset.prod_mul_distrib]
  refine congrArg (· • wordMonomial K u) (congrArg _ (Finset.prod_congr rfl fun i _ => ?_))
  rw [superScalar_superWord]
  cases ε i with
  | false => rw [Bool.cond_false, Bool.cond_false, signFactor_false, one_mul]
  | true => rw [Bool.cond_true, Bool.cond_true, signFactor_true, mul_neg_one]

/-- **The sum over the signs factorises.** For any set `R` of pairs of positions
and any word `u` of absolute values,
`∑_{v ∈ 𝒜^n, |v| = u}q^{inv^±(R,v)}z_v = q^{inv(R,u)}x_u∏_{i}(q - q^{d_i(R,u)})`.

The block `{v : |v| = u}` is indexed by the sign tuples, so the left-hand side is a sum of `2^n`
terms; at each of them `HJO.Dyck.pow_superInvNumber_smul_superMonomial_superWord` pulls out the
common `q^{inv(R,u)}x_u` and leaves a product over the positions whose factor at a position depends
only on the sign there. The signs vary independently, so summing the product over the `2^n` tuples
is expanding a product of `n` binomials, and the binomial at a position is
`HJO.Sym.sum_signFactor`.

The hypothesis that the pairs of `R` increase, and the positivity of the entries of
`u`, are both unused and dropped. -/
@[hjo "lem_cm_sign_sum"]
theorem sum_pow_superInvNumber_smul_superMonomial (K : Type*) [CommRing K] (q : K) {n : ℕ}
    (R : Finset (Fin n × Fin n)) (u : Fin n → ℕ) :
    ∑ v ∈ superFibre u, q ^ superInvNumber R v • superMonomial K q v
      = (q ^ invNumber R u * ∏ i, (q - q ^ equalPartners R u i)) • wordMonomial K u := by
  rw [superFibre_eq_image, Finset.sum_image fun ε _ ε' _ h => superWord_injective u h,
    Finset.sum_congr rfl fun ε _ => pow_superInvNumber_smul_superMonomial_superWord q R u ε,
    ← Finset.sum_smul, ← Finset.mul_sum, ← Fintype.piFinset_univ, Finset.sum_prod_piFinset]
  exact congrArg (· • wordMonomial K u)
    (congrArg _ (Finset.prod_congr rfl fun i _ => sum_signFactor q _))

end HJO.Dyck
