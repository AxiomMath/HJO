/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.PlethysticAlphabet
public import HJO.Shuffle.SweepModule
public meta import HJO.Attr

/-! # The twisted complete homogeneous identity

`HJO.Sweep.braid_add_q_completeHomog_twist` reads: for every `b ≥ 1`, on `V_k` with `k ≥ 2`,
`(T_1 + q) h_b[u(1-q)y_1] = h_b[u(1-q)(y_1+y_2)]`. This file makes both sides honest elements of
the total space `HJO.Sweep.Total L` of `HJO.Shuffle.SweepModule` and proves the identity.

## The two alphabets

A plethystic substitution `F ↦ F[Z]` is a ring homomorphism out of `Λ`, so it is determined by the
images of the power sums. `HJO.Sweep.alphabetEval` packages that: given a family
`P : ℕ → Total L`, it is the `L`-algebra map `Λ → V_*` sending `p_r` to `P r`. The two
alphabets are then `HJO.Sweep.twistLetter`, the single virtual letter `u(1-q)y_i`, and
`HJO.Sweep.twistLetterPair`, its two-letter companion `u(1-q)(y_1+y_2)`.

**The exponent is `1 - q^r` and not `(1-q)^r`.** The letter `u(1-q)y_i` is the *virtual* alphabet
`uy_i - quy_i`, in whose lambda ring `p_r = (uy_i)^r - (quy_i)^r = u^r(1-q^r)y_i^r`. This is the
same reading `HJO.Sweep.qshift` records at length for `(q-1)y_i` — `p_r[(q-1)y] = (q^r-1)y^r` — and
it is not cosmetic: under the monomial reading `p_r ↦ u^r(1-q)^r y_i^r` both plethysms become
honest powers of `u(1-q)y_i`, and at `b = 2` the identity would read
`u^2(1-q)^2(y_1^2 + y_2^2 + (1-q)y_1y_2) = u^2(1-q)^2(y_1^2 + y_1y_2 + y_2^2)`, false on the
coefficient of `y_1y_2` unless `q = 0`.

## The `b = 0` failure

The statement begins at `b = 1` and cannot be extended. At `b = 0` both plethysms are `h_0 = 1`, so
the left side is `(T_1 + q)(1) = 1 + q` while the right side is `1`: the identity fails by exactly
`q`. Its one use, the second starred commutator relation, uses only the coefficients with
`b > 0` and disposes of `b = 0` separately.

## Main results

* `HJO.Sweep.alphabetEval`: the plethystic substitution `F ↦ F[Z]` determined by the power sums of
  `Z`, as an `L`-algebra map `Λ → V_*`.
* `HJO.Sweep.alphabetEval_twistLetter_completeHomog`: `h_b[u(1-q)y_i] = (1-q)u^b y_i^b` for
  `b ≥ 1`, the one-letter evaluation the proof opens with.
* `HJO.Sweep.braid_add_scal_q_auxVar_pow`:
  `(T_1 + q)(y_1^b) = y_1^b + y_2^b + (1-q)∑_{j=1}^{b-1} y_1^j y_2^{b-j}`, the monomial computation
  behind the identity.
* `HJO.Sweep.braid_add_q_completeHomog_twist`.

## Implementation notes

The statement as usually written says "on `V_k` with `k ≥ 2`". On this one-total-space presentation
that carries no content and both hypotheses are dropped: the two sides are elements of `Total L`,
and `T_1` is an endomorphism of that one space rather than a family of maps `V_k → V_k`. The
hypotheses are recoverable as membership statements — both alphabets use only `y_1` and `y_2`, so
both sides lie in `HJO.Sweep.piece L k` for every `k ≥ 2`, and `HJO.Sweep.braid_mem_piece` carries
`T_1` across it — so nothing is lost by stating the equality in the total space, which is where its
one use, `HJO.Sweep.braidInv_starCommCM_dplusStar`, composes it with the other operators anyway.
Only `b ≥ 1` survives as a hypothesis, and it is genuinely needed.

The one-letter value is `HJO.Sym.completeHomog_dilate_letter` applied
with `x = u y_i`, and the two-letter expansion is `HJO.Sym.completeHomog_add_alphabet` applied to
the pair of one-letter alphabets. What remains is the monomial computation of `(T_1 + q)(y_1^b)`,
which comes from `HJO.Sweep.dividedDiff_unique` together with Mathlib's `geom_sum₂_mul`, and a
reflection `s ↦ b - s` matching the two middle sums.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, §5. -/

@[expose] public section

namespace HJO.Sweep

open MvPolynomial

section Basic

variable {L : Type*} [Field L]

/-- A scalar power read in the total space: `scal` is a ring homomorphism. -/
theorem scal_pow (x : L) (n : ℕ) : (scal (x ^ n) : Total L) = scal x ^ n := by
  rw [scal_eq_algebraMap, scal_eq_algebraMap, map_pow]

/-! ### The monomial computation of `(T_1 + q)(y_1^b)` -/

/-- **The divided difference of a power of `y_1`.**
`∂_1(y_1^b) = -∑_{i=0}^{b-1} y_1^i y_2^{b-1-i}`, by `dividedDiff_unique` from the geometric
factorisation `(∑_{i<b} y_1^i y_2^{b-1-i})(y_1 - y_2) = y_1^b - y_2^b`. -/
theorem dividedDiff_one_auxVar_pow (b : ℕ) :
    dividedDiff 1 ((auxVar 1 : Total L) ^ b)
      = -∑ i ∈ Finset.range b, (auxVar 1 : Total L) ^ i * auxVar 2 ^ (b - 1 - i) := by
  refine (dividedDiff_unique (i := 1) le_rfl ?_).symm
  have hs : swapAux L 1 ((auxVar 1 : Total L) ^ b) = auxVar 2 ^ b := by
    rw [map_pow, swapAux_auxVar_self le_rfl]
  have hg := geom_sum₂_mul (auxVar 1 : Total L) (auxVar 2) b
  rw [hs, ← auxVar_one, ← auxVar_two]
  linear_combination hg

/-- **The monomial computation.**
`(T_1 + q)(y_1^{m+1}) = y_1^{m+1} + y_2^{m+1} + (1-q)∑_{i=0}^{m-1} y_1^{i+1} y_2^{m-i}`, which is
the displayed formula of the proof with the outer factor `(1-q)u^b` stripped off. The
`i = m` term of `y_1 ∂_1(y_1^{m+1})` is `y_1^{m+1}` itself, and it is that term which combines with
`q y_1^{m+1}` to leave the bare `y_1^{m+1}` above; the remaining `m` terms carry the factor
`1 - q`. -/
theorem braid_add_scal_q_auxVar_pow (q : L) (m : ℕ) :
    braid q 1 ((auxVar 1 : Total L) ^ (m + 1)) + scal q * auxVar 1 ^ (m + 1)
      = auxVar 1 ^ (m + 1) + auxVar 2 ^ (m + 1)
        + scal (1 - q) * ∑ i ∈ Finset.range m,
            (auxVar 1 : Total L) ^ (i + 1) * auxVar 2 ^ (m - i) := by
  have hs : swapAux L 1 ((auxVar 1 : Total L) ^ (m + 1)) = auxVar 2 ^ (m + 1) := by
    rw [map_pow, swapAux_auxVar_self le_rfl]
  have hsum : (auxVar 1 : Total L) * ∑ i ∈ Finset.range (m + 1),
        (auxVar 1 : Total L) ^ i * auxVar 2 ^ (m + 1 - 1 - i)
      = (∑ i ∈ Finset.range m, (auxVar 1 : Total L) ^ (i + 1) * auxVar 2 ^ (m - i))
        + auxVar 1 ^ (m + 1) := by
    rw [Finset.mul_sum, Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · ring
  have h1 : (scal (1 - q) : Total L) = -scal (q - 1) := by
    rw [show (1 : L) - q = -(q - 1) by ring, scal_neg]
  have h2 : (scal q : Total L) = 1 + scal (q - 1) := by
    rw [← scal_one (L := L), ← scal_add]
    congr 1
    ring
  rw [braid_apply, hs, dividedDiff_one_auxVar_pow, h1, h2]
  linear_combination (-scal (q - 1) : Total L) * hsum

/-! ### Plethystic substitution into the total space -/

/-- **Plethystic substitution.** The `L`-algebra map `Λ → V_*` substituting for the alphabet whose
`r`-th power sum is `P r`, i.e. the operation `F ↦ F[Z]` for a virtual alphabet `Z` presented by
its power sums. It is well defined because `Λ = L[p_1, p_2, …]` is a polynomial algebra on the
power sums.

This is *not* the `Γ_+` of `HJO.Sweep.alphabetShift`, which is `F ↦ F[X + Z]`. -/
noncomputable def alphabetEval (P : ℕ → Total L) : Sym.Lambda L →ₐ[L] Total L :=
  MvPolynomial.aeval fun j => P (j + 1)

/-- The substitution on a generator of `Λ`: the generator with index `j` stands for `p_{j+1}`. -/
@[simp] theorem alphabetEval_X (P : ℕ → Total L) (j : ℕ) :
    alphabetEval P (MvPolynomial.X j) = P (j + 1) := by
  rw [alphabetEval, MvPolynomial.aeval_X]

/-- The substitution sends `p_r` to `P r`, for `r ≥ 1`. The positivity hypothesis is the truncated
subtraction in `HJO.Sym.powerSum`: `powerSum L 0` and `powerSum L 1` are the same generator. -/
theorem alphabetEval_powerSum (P : ℕ → Total L) {r : ℕ} (hr : 0 < r) :
    alphabetEval P (Sym.powerSum L r) = P r := by
  rw [Sym.powerSum, alphabetEval_X]
  congr 1
  omega

/-- **The single virtual letter `u(1-q)y_i`**, presented by its power sums
`p_r = u^r(1 - q^r) y_i^r`. The exponent is `1 - q^r`, not `(1-q)^r`: the letter is the virtual
alphabet `uy_i - quy_i`, exactly as `HJO.Sweep.qshift` records for `(q-1)y_i`. -/
noncomputable def twistLetter (u q : L) (i : ℕ) : ℕ → Total L :=
  fun r => scal (u ^ r * (1 - q ^ r)) * auxVar i ^ r

/-- **The two-letter alphabet `u(1-q)(y_1+y_2)`**, presented by its power sums
`p_r = u^r(1 - q^r)(y_1^r + y_2^r)`: the sum of the two alphabets `u(1-q)y_1` and `u(1-q)y_2`. -/
noncomputable def twistLetterPair (u q : L) : ℕ → Total L :=
  fun r => scal (u ^ r * (1 - q ^ r)) * (auxVar 1 ^ r + auxVar 2 ^ r)

/-- The power sums of the single virtual letter, in the shape `HJO.Sym.completeHomog_dilate_letter`
asks for: `p_r[u(1-q)y_i] = (1 - q^r)(u y_i)^r`. -/
theorem alphabetEval_twistLetter_powerSum (u q : L) (i : ℕ) {j : ℕ} (hj : 0 < j) :
    alphabetEval (twistLetter u q i) (Sym.powerSum L j)
      = (1 - scal q ^ j) * (scal u * auxVar i) ^ j := by
  rw [alphabetEval_powerSum _ hj, twistLetter]
  simp only [scal_mul, scal_sub, scal_one, scal_pow, mul_pow]
  ring

end Basic

/-! ### The identity -/

section Homog

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- The value of any plethystic substitution on `h_0 = 1`. -/
theorem alphabetEval_completeHomog_zero (P : ℕ → Total L) :
    alphabetEval P (Sym.completeHomog L 0) = 1 := by
  rw [CopPower.completeHomog_zero, map_one]

/-- **`h_b[u(1-q)y_i] = (1-q) u^b y_i^b` for `b ≥ 1`**, the value the proof opens with.
It is `HJO.Sym.completeHomog_dilate_letter` at the letter `u y_i`: the
scalar `1 - q` is the same in every positive degree, and it is the plethystic value, not the
monomial one. At `b = 0` the value is instead `1`. -/
theorem alphabetEval_twistLetter_completeHomog (u q : L) (i : ℕ) {b : ℕ} (hb : 0 < b) :
    alphabetEval (twistLetter u q i) (Sym.completeHomog L b)
      = scal ((1 - q) * u ^ b) * auxVar i ^ b := by
  have h := Sym.completeHomog_dilate_letter (K := L) (R := Total L)
    (F := Sym.Lambda L →ₐ[L] Total L) (alphabetEval (twistLetter u q i)) (scal q)
    (scal u * auxVar i) (fun j hj => alphabetEval_twistLetter_powerSum u q i hj) hb
  rw [h]
  simp only [scal_mul, scal_sub, scal_one, scal_pow, mul_pow]
  ring

/-- **The two-letter expansion.**
`h_b[u(1-q)(y_1+y_2)] = ∑_{s=0}^{b} h_{b-s}[u(1-q)y_1] h_s[u(1-q)y_2]`, by
`HJO.Sym.completeHomog_add_alphabet`, the pair alphabet being the sum of the two single letters. -/
theorem alphabetEval_twistLetterPair_completeHomog (u q : L) (b : ℕ) :
    alphabetEval (twistLetterPair u q) (Sym.completeHomog L b)
      = ∑ s ∈ Finset.range (b + 1),
          alphabetEval (twistLetter u q 1) (Sym.completeHomog L (b - s))
            * alphabetEval (twistLetter u q 2) (Sym.completeHomog L s) := by
  refine Sym.completeHomog_add_alphabet (K := L) (R := Total L)
    (F := Sym.Lambda L →ₐ[L] Total L) (G := Sym.Lambda L →ₐ[L] Total L)
    (H := Sym.Lambda L →ₐ[L] Total L) (alphabetEval (twistLetter u q 1))
    (alphabetEval (twistLetter u q 2)) (alphabetEval (twistLetterPair u q))
    (fun j hj => ?_) b
  rw [alphabetEval_powerSum _ hj, alphabetEval_powerSum _ hj, alphabetEval_powerSum _ hj,
    twistLetter, twistLetter, twistLetterPair]
  ring

/-- **The twisted complete homogeneous identity.** `HJO.Sweep.braid_add_q_completeHomog_twist`: for
`b ≥ 1`, `(T_1 + q) h_b[u(1-q)y_1] = h_b[u(1-q)(y_1+y_2)]`, with `T_1` the braid operator
`HJO.Sweep.braid q 1` of `HJO.Sweep.braid` and `h_b[·]` the plethystic substitutions
`HJO.Sweep.alphabetEval` above.

The proof is the standard one. The left side is `(1-q)u^b` times `(T_1+q)(y_1^b)`, which
`braid_add_scal_q_auxVar_pow` computes as `y_1^b + y_2^b + (1-q)∑_{j=1}^{b-1} y_1^j y_2^{b-j}`; the
right side expands over the two letters as
`(1-q)u^b(y_1^b + y_2^b) + (1-q)^2u^b∑_{s=1}^{b-1} y_1^{b-s} y_2^s`, the extreme terms coming from
`h_0 = 1` on one of the two letters. The two middle sums agree under `s ↦ b - s`.

**Why `b ≥ 1`.** At `b = 0` both plethysms are `h_0 = 1`, so the left side is `1 + q` and the right
side is `1`: the identity fails by `q`. The hypotheses "`k ≥ 2`" and "on `V_k`" are
dropped as carrying no content here — see this file's implementation notes — but `b ≥ 1` is real. -/
@[hjo "lem_cm_hb_twist"]
theorem braid_add_q_completeHomog_twist (q u : L) {b : ℕ} (hb : 0 < b) :
    braid q 1 (alphabetEval (twistLetter u q 1) (Sym.completeHomog L b))
        + scal q * alphabetEval (twistLetter u q 1) (Sym.completeHomog L b)
      = alphabetEval (twistLetterPair u q) (Sym.completeHomog L b) := by
  obtain ⟨m, rfl⟩ : ∃ m, b = m + 1 := ⟨b - 1, by omega⟩
  -- the middle terms of the two-letter expansion
  have emid : ∀ s ∈ Finset.range m,
      alphabetEval (twistLetter u q 1) (Sym.completeHomog L (m + 1 - (s + 1)))
          * alphabetEval (twistLetter u q 2) (Sym.completeHomog L (s + 1))
        = scal ((1 - q) ^ 2 * u ^ (m + 1))
            * ((auxVar 1 : Total L) ^ (m - s) * auxVar 2 ^ (s + 1)) := by
    intro s hs
    have hsm : s < m := Finset.mem_range.mp hs
    have hidx : m + 1 - (s + 1) = m - s := by omega
    have hu : u ^ (m - s) * u ^ (s + 1) = u ^ (m + 1) := by
      rw [← pow_add]
      congr 1
      omega
    have hc : (scal ((1 - q) * u ^ (m - s)) : Total L) * scal ((1 - q) * u ^ (s + 1))
        = scal ((1 - q) ^ 2 * u ^ (m + 1)) := by
      rw [← scal_mul]
      congr 1
      linear_combination (1 - q) ^ 2 * hu
    rw [hidx, alphabetEval_twistLetter_completeHomog u q 1 (by omega),
      alphabetEval_twistLetter_completeHomog u q 2 (by omega), ← hc]
    ring
  -- the two-letter expansion, with the extreme terms peeled off
  have hR : alphabetEval (twistLetterPair u q) (Sym.completeHomog L (m + 1))
      = scal ((1 - q) ^ 2 * u ^ (m + 1))
            * ∑ s ∈ Finset.range m, (auxVar 1 : Total L) ^ (m - s) * auxVar 2 ^ (s + 1)
        + scal ((1 - q) * u ^ (m + 1)) * (auxVar 1 : Total L) ^ (m + 1)
        + scal ((1 - q) * u ^ (m + 1)) * (auxVar 2 : Total L) ^ (m + 1) := by
    rw [alphabetEval_twistLetterPair_completeHomog, Finset.sum_range_succ,
      Finset.sum_range_succ', Finset.sum_congr rfl emid, ← Finset.mul_sum]
    simp only [Nat.sub_zero, Nat.sub_self]
    rw [alphabetEval_twistLetter_completeHomog u q 1 (b := m + 1) (by omega),
      alphabetEval_twistLetter_completeHomog u q 2 (b := m + 1) (by omega),
      alphabetEval_completeHomog_zero, alphabetEval_completeHomog_zero]
    ring
  -- the reflection `s ↦ b - s` matching the two middle sums
  have hT : ∑ i ∈ Finset.range m, (auxVar 1 : Total L) ^ (i + 1) * auxVar 2 ^ (m - i)
      = ∑ s ∈ Finset.range m, (auxVar 1 : Total L) ^ (m - s) * auxVar 2 ^ (s + 1) := by
    refine (Finset.sum_range_reflect
      (fun i => (auxVar 1 : Total L) ^ (i + 1) * auxVar 2 ^ (m - i)) m).symm.trans
        (Finset.sum_congr rfl fun s hs => ?_)
    have hsm : s < m := Finset.mem_range.mp hs
    have h1 : m - 1 - s + 1 = m - s := by omega
    have h2 : m - (m - 1 - s) = s + 1 := by omega
    rw [h1, h2]
  have key := braid_add_scal_q_auxVar_pow (L := L) q m
  rw [alphabetEval_twistLetter_completeHomog u q 1 (b := m + 1) (by omega), braid_scal_mul, hR,
    ← hT]
  simp only [scal_mul, scal_sub, scal_one, scal_pow] at key ⊢
  linear_combination ((1 - scal q : Total L) * scal u ^ (m + 1)) * key

end Homog

end HJO.Sweep
