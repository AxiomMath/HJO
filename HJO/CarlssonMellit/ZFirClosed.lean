/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.ChiPrimeCoeffSymmetric
public import HJO.CarlssonMellit.ZFir
public import HJO.PlethysticAlphabet
public meta import HJO.Attr

/-! # The closed form of the iterated swapping coefficients

Two lemmas. The closed form `HJO.Sym.zSwapCoeff_succ_eq_mul_completeHomog`, displayed as
`HJO.Sym.one_sub_C_scalarFrac_mul_zSwapCoeff`: for `i ≥ 1` and `r ≥ 0`,

`f_{i,r} = (h_i[(1-q)X_r] - h_i[(1-q)X_{r-1}]) / (1-q)`,

with `f_{i,r}` the iterated swapping coefficients `HJO.Sym.zSwapCoeff` of `HJO.CarlssonMellit.ZFir`
and `X_r = y_k + x_1 + ⋯ + x_r` the truncated alphabets of `HJO.Sym.truncatedAlphabet`. And
`HJO.Sym.isZDelta_zLetterSeries_pow_succ` **at the merged letters**, which needs a separate
argument: the composite defining `f_{i,r}` applies the swapping operator at the pair `(y_k, x_1)` in
its first step, where the left letter is the distinguished letter and not a free variable, so the
earlier lemma `HJO.Sym.xdelta_X_pow_succ` — about two free variables and about `HJO.Sym.xdelta` —
does not cover it.

## The key identity

One ring identity, `HJO.Sym.sub_mul_mul_completeHomog_twist_add_letter`: in any commutative ring,
for `φ` the alphabet `(1-Q)u + v`,

`(v - u)·(v·h_n[(1-Q)u + v]) = (Q-1)v u^{n+1} + (v - Qu)v^{n+1}`.

The right-hand side is the numerator of the defining equation of the swapping operator at `u^{n+1}`.
So `HJO.Sym.isZDelta_zLetterSeries_pow_succ` holds at *every* pair of letters at once, and the
difference between the two cases is only what one does with the identity afterwards. At two free
variables one divides, which is why `HJO.Sym.xdelta_X_pow_succ` needs `x_{r+1} - x_r` to be a
non-zerodivisor. At two letters of the merged alphabet there is nothing to divide:
`HJO.Sym.IsZDelta` *is* that equation, and `HJO.Sym.isZDelta_zLetterSeries_pow_succ` is the identity
read as an instance of it, with the offset-`0` case — the operator `Δ_{y_k,x_1}` — included and
needing no separate argument. That is the whole argument; nothing about `HJO.Sym.xdelta` on the
merged alphabet is asserted, and no bridge between the two operators is needed.

## Main results

* `HJO.Sym.sub_mul_mul_completeHomog_twist_add_letter`: the ring identity above.
* `HJO.Sym.isZDelta_zLetterSeries_pow_succ` at the merged letters.
* `HJO.Sym.zSwapCoeff_succ_eq_mul_completeHomog` in the form the proof
  derives and inducts on, `f_{i,t} = z_t·h_{i-1}[(1-q)X_{t-1} + z_t]`.
* `HJO.Sym.one_sub_C_scalarFrac_mul_zSwapCoeff`: the closed form as displayed above,
  `(1-q)f_{i,t} = h_i[(1-q)X_t] - h_i[(1-q)X_{t-1}]`.
* `HJO.Sym.exists_ringHom_powerSum_eq_truncTwist_add_letter`,
  `HJO.Sym.exists_ringHom_powerSum_eq_truncTwist`: the two families of alphabets exist, so neither
  statement is vacuous.
* `HJO.Sym.zSwapFixedSubring`, `HJO.Sym.mem_zSwapFixedSubring_of_forall`: the members of
  `Z^{(k+1)}` fixed by *one* interchange, and the criterion that a homomorphism out of `Λ` lands
  there.

## Implementation notes

*The division by `1-q` is not performed, and the proof does not perform it either.*
`1-q` is not a unit of `P°_{k+1}` for a general base, so the displayed quotient is stated as
`(1-q)f_{i,t} = h_i[(1-q)X_t] - h_i[(1-q)X_{t-1}]`. Nothing is weakened: the
derivation computes the numerator and factors `1-q` out of it, never inverting it, and
`HJO.Sym.zSwapCoeff_succ_eq_mul_completeHomog` is the quotient itself in the division-free form
`z_t·h_{i-1}[(1-q)X_{t-1} + z_t]` that the proof rewrites the display into on its first line
and then inducts on.

*The alphabets are hypotheses, not constructions*, as in `HJO.CarlssonMellit.DeltaUpow`: an
alphabet is a ring homomorphism out of `Λ`, named by its values on the power sums, and the
statements below quantify over every family with those values. The existence statements are
separate, so nothing has to be unfolded to use the identities. The scalars are pinned to the
constants of `𝕂(y₁, …, y_k)`, which is what makes the *coefficients* of the closed form lie in
`Z^{(k+1)}` and be fixed by the interchange.

*What the inductive step needs, and the subring that supplies it.* The step writes
`z_r·h_n[(1-q)X_{r-1} + z_r]` as `∑_{s ≤ n}h_{n-s}[(1-q)X_{r-1}]·z_r^{s+1}` by
`HJO.Sym.completeHomog_add_alphabet`, and applies the operator to each summand: the coefficient
`h_{n-s}[(1-q)X_{r-1}]` is passed by `HJO.Sym.isZDelta_mul_of_zSwap_eq`, which asks it to lie in
`Z^{(k+1)}` and be fixed by `ŝ_m`, and the power of `z_r` is handled by
`HJO.Sym.isZDelta_zLetterSeries_pow_succ`. `HJO.Sym.zSymmSubring` is the wrong home for those
coefficients — they are *not* fixed by every relabelling, only by the ones that move no letter below
the offset `r` — so `HJO.Sym.zSwapFixedSubring` is introduced for one interchange, and
`HJO.Sym.mem_zSwapFixedSubring_of_forall` reduces membership to the scalars and the variables of `Λ`
by `MvPolynomial.induction_on`. The whole of the closure is then the `Subring` API.

*No `ℕ`-subtraction on the index `i`.* The hypothesis `i ≥ 1` is written `i = n + 1`, so `h_{i-1}`
is `h_n`; the truncated alphabets are indexed by the number of letters, so `X_{r-1}` is the alphabet
of the letters at offsets `0, …, r-1` and the alphabet `X_{-1} = 0` is the empty one at `r = 0`,
with no subtraction anywhere.

*The three `Δ` operators, and which one this is.* The operator composed in `HJO.Sym.zSwapCoeff` is
the `Δ_m` of `HJO.Sym.IsZDelta` on the merged alphabet, recorded at `HJO.Sym.X_sub_X_mul_xdelta`;
`HJO.Sym.pdelta` and `HJO.Sym.xdelta` are the other two and neither appears here.

## References

Lemmas `HJO.Sym.zSwapCoeff_succ_eq_mul_completeHomog` and `HJO.Sym.isZDelta_zLetterSeries_pow_succ`,
with `HJO.Sym.completeHomog`, `HJO.Sym.truncatedAlphabet`, `HJO.Sym.zSwapCoeff`, `HJO.Sym.IsZDelta`,
`HJO.Sym.completeHomog_dilate_letter`, `HJO.Sym.completeHomog_add_alphabet`,
`HJO.Sym.eq_of_isZDelta`, `HJO.Sym.zDeltaOn` and `HJO.Sym.isZDelta_mul_of_zSwap_eq`; the identity
`HJO.Sym.xdelta_X_pow_succ` at two free variables is needed outside its stated scope, at the merged
letters, which is what `HJO.Sym.isZDelta_zLetterSeries_pow_succ` supplies. Used by
`HJO.Sym.one_sub_C_scalarFrac_mul_summableSum_zSwapCoeff`. E. Carlsson and A. Mellit, *A proof of
the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 4, where both
identities are asserted without proof.
-/

@[expose] public section

namespace HJO.Sym

/-! ### The swapping identity on a power of the left letter, as a ring identity -/

/-- **The algebraic core of `HJO.Sym.isZDelta_zLetterSeries_pow_succ`**, with no power series and no
division in it: in any commutative ring, if `φ` is the alphabet `(1-Q)u + v` — a ring homomorphism
out of `Λ` sending each power sum `p_j`, `j ≥ 1`, to `(1 - Q^j)u^j + v^j` — then

`(v - u)·(v·h_n[(1-Q)u + v]) = (Q-1)v u^{n+1} + (v - Qu)v^{n+1}`.

The right-hand side is the numerator of the defining equation of the swapping operator at the
argument `u^{n+1}`, the interchange of `u` and `v` carrying `u^{n+1}` to `v^{n+1}`. So this one
identity is `HJO.Sym.isZDelta_zLetterSeries_pow_succ` at *every* pair of letters at once: at two
free variables it is `HJO.Sym.xdelta_X_pow_succ`, where the factor `v - u` is cancelled because it
is a non-zerodivisor, and at two letters of the merged alphabet it is
`HJO.Sym.isZDelta_zLetterSeries_pow_succ`, where no cancellation happens at all — the operator there
is *defined* by this equation.

Proof: `h_n[(1-Q)u + v] = v^n + (1-Q)u∑_{s<n}v^s u^{n-1-s}` by
`HJO.Sym.completeHomog_add_alphabet` and `HJO.Sym.completeHomog_dilate_letter`, and the geometric
identity `(∑_{s<n}v^su^{n-1-s})(v-u) = v^n - u^n` turns the product into the numerator. -/
theorem sub_mul_mul_completeHomog_twist_add_letter {R : Type*} [CommRing R] {A : Type*}
    [CommRing A] [Algebra ℚ A] {F : Type*} [FunLike F (Lambda A) R] [RingHomClass F (Lambda A) R]
    (φ : F) (Q u v : R) (n : ℕ)
    (hφ : ∀ j : ℕ, 0 < j → φ (powerSum A j) = (1 - Q ^ j) * u ^ j + v ^ j) :
    (v - u) * (v * φ (completeHomog A n))
      = (Q - 1) * v * u ^ (n + 1) + (v - Q * u) * v ^ (n + 1) := by
  set base : A →+* R := (φ : Lambda A →+* R).comp MvPolynomial.C with hbase
  set ι : Lambda A →+* R :=
    MvPolynomial.eval₂Hom base (fun i => (1 - Q ^ (i + 1)) * u ^ (i + 1)) with hι
  have hιX : ∀ i : ℕ, ι (MvPolynomial.X i) = (1 - Q ^ (i + 1)) * u ^ (i + 1) :=
    fun i => by rw [hι, MvPolynomial.eval₂Hom_X']
  have hιp : ∀ j : ℕ, 0 < j → ι (powerSum A j) = (1 - Q ^ j) * u ^ j := by
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [CopPower.powerSum_succ, hιX i]
  have hιh : ∀ b : ℕ, 0 < b → ι (completeHomog A b) = (1 - Q) * u ^ b :=
    fun b hb => completeHomog_dilate_letter ι _ _ hιp hb
  set ν : Lambda A →+* R := MvPolynomial.eval₂Hom base (fun i => v ^ (i + 1)) with hν
  have hνX : ∀ i : ℕ, ν (MvPolynomial.X i) = v ^ (i + 1) :=
    fun i => by rw [hν, MvPolynomial.eval₂Hom_X']
  have hνp : ∀ j : ℕ, 0 < j → ν (powerSum A j) = v ^ j := by
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [CopPower.powerSum_succ, hνX i]
  have hνh : ∀ s : ℕ, ν (completeHomog A s) = v ^ s := completeHomog_single_letter ν _ hνp
  have hadd : ∀ j : ℕ, 0 < j → φ (powerSum A j) = ι (powerSum A j) + ν (powerSum A j) := by
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [hφ _ hj, CopPower.powerSum_succ, hιX i, hνX i]
  have hsum : φ (completeHomog A n)
      = (∑ s ∈ Finset.range n, ι (completeHomog A (n - s)) * ν (completeHomog A s)) + v ^ n := by
    rw [completeHomog_add_alphabet ι ν φ hadd n, Finset.sum_range_succ, Nat.sub_self,
      CopPower.completeHomog_zero, map_one, one_mul, hνh n]
  have hT : (∑ s ∈ Finset.range n, ι (completeHomog A (n - s)) * ν (completeHomog A s))
      = (1 - Q) * u * ∑ s ∈ Finset.range n, v ^ s * u ^ (n - 1 - s) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' : s < n := Finset.mem_range.mp hs
    rw [hιh (n - s) (by omega), hνh s, show n - s = n - 1 - s + 1 from by omega, pow_succ]
    ring
  have hgeom : (∑ s ∈ Finset.range n, v ^ s * u ^ (n - 1 - s)) * (v - u) = v ^ n - u ^ n :=
    geom_sum₂_mul _ _ n
  rw [hsum, hT]
  linear_combination ((1 - Q) * u * v) * hgeom

/-! ### The letters the interchange fixes -/

variable {K : Type*} [CommRing K] [IsDomain K] {k : ℕ}

/-- **The interchange fixes every letter but the two it moves.** `ŝ_m` relabels along the
transposition of the letters at offsets `r` and `r + 1`, so a letter at any other offset is
untouched, the offsets naming distinct letters by `HJO.Sym.zLetter_injective`. -/
@[simp]
theorem zSwap_zLetterSeries_of_ne {r s : ℕ} (hs : s ≠ r) (hs' : s ≠ r + 1) :
    zSwap K k r (zLetterSeries K k s) = zLetterSeries K k s := by
  have h : zLetterSeries K k s = zMonomial K k (Finsupp.single (zLetter s) 1) 1 := rfl
  rw [h, zSwap_zMonomial]
  refine congrArg (fun ν => zMonomial K k ν (1 : AuxFrac K k)) (Finsupp.ext fun a => ?_)
  rw [Finsupp.equivMapDomain_apply, zSwapEquiv, Equiv.symm_swap]
  rcases eq_or_ne a (zLetter r) with rfl | ha
  · rw [Equiv.swap_apply_left,
      Finsupp.single_eq_of_ne fun h => hs' (zLetter_injective h).symm,
      Finsupp.single_eq_of_ne fun h => hs (zLetter_injective h).symm]
  · rcases eq_or_ne a (zLetter (r + 1)) with rfl | ha'
    · rw [Equiv.swap_apply_right,
        Finsupp.single_eq_of_ne fun h => hs (zLetter_injective h).symm,
        Finsupp.single_eq_of_ne fun h => hs' (zLetter_injective h).symm]
    · rw [Equiv.swap_apply_of_ne_of_ne ha ha']

/-- `Z^{(k+1)}` is closed under powers, being a subring. -/
theorem pow_mem_zRing {G : AuxAlphabetSeriesFrac K (k + 1)} (hG : G ∈ zRing K k) (n : ℕ) :
    G ^ n ∈ zRing K k := by
  induction n with
  | zero => rw [pow_zero]; exact one_mem_zRing
  | succ n ih => rw [pow_succ]; exact mul_mem_zRing ih hG

/-- `ŝ_m` is multiplicative on `Z^{(k+1)}`, so it commutes with powers there. -/
theorem zSwap_pow_of_mem_zRing {G : AuxAlphabetSeriesFrac K (k + 1)} (r : ℕ) (hG : G ∈ zRing K k)
    (n : ℕ) : zSwap K k r (G ^ n) = zSwap K k r G ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, zSwap_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, zSwap_apply, zPerm_mul_of_mem_zRing _ (pow_mem_zRing hG n) hG,
      ← zSwap_apply, ← zSwap_apply, ih]

/-! ### Elements of `Z^{(k+1)}` fixed by one interchange -/

/-- **The subring of `Z^{(k+1)}` fixed by one interchange `ŝ_m`.** `HJO.Sym.zSymmSubring` asks to be
fixed by *every* relabelling, which the coefficients of the closed form below are not — they involve
the letters below the offset `r` and nothing else, so the interchange at `r` fixes them while others
do not. That `ŝ_m` is a ring homomorphism on `Z^{(k+1)}` is `HJO.Sym.zPermEquiv`, which is what
makes this a subring and gives every closure property the induction below needs for free. -/
noncomputable def zSwapFixedSubring (K : Type*) [CommRing K] [IsDomain K] (k r : ℕ) :
    Subring (AuxAlphabetSeriesFrac K (k + 1)) where
  carrier := {F | F ∈ zRing K k ∧ zSwap K k r F = F}
  one_mem' := ⟨one_mem_zRing, zSwap_one r⟩
  mul_mem' hF hH := ⟨mul_mem_zRing hF.1 hH.1, by
    rw [zSwap_apply, zPerm_mul_of_mem_zRing _ hF.1 hH.1, ← zSwap_apply, ← zSwap_apply, hF.2, hH.2]⟩
  zero_mem' := ⟨zero_mem_zRing, by rw [zSwap_apply, zPerm_zero]⟩
  add_mem' hF hH := ⟨add_mem_zRing hF.1 hH.1, by
    rw [zSwap_apply, zPerm_add_of_mem_zRing _ hF.1 hH.1, ← zSwap_apply, ← zSwap_apply, hF.2, hH.2]⟩
  neg_mem' hF := ⟨neg_mem_zRing hF.1, by
    rw [zSwap_apply, zPerm_neg_of_mem_zRing _ hF.1, ← zSwap_apply, hF.2]⟩

@[simp]
theorem mem_zSwapFixedSubring {r : ℕ} {F : AuxAlphabetSeriesFrac K (k + 1)} :
    F ∈ zSwapFixedSubring K k r ↔ F ∈ zRing K k ∧ zSwap K k r F = F :=
  Iff.rfl

/-- What every relabelling fixes, one interchange fixes. -/
theorem zSymmSubring_le_zSwapFixedSubring (K : Type*) [CommRing K] [IsDomain K] (k r : ℕ) :
    zSymmSubring K k ≤ zSwapFixedSubring K k r :=
  fun _ hF => ⟨hF.1, hF.2 (zSwapEquiv r)⟩

/-- A letter of the merged alphabet at an offset the interchange does not move is fixed by it. -/
theorem zLetterSeries_mem_zSwapFixedSubring {r s : ℕ} (hs : s ≠ r) (hs' : s ≠ r + 1) :
    zLetterSeries K k s ∈ zSwapFixedSubring K k r :=
  ⟨zLetterSeries_mem_zRing s, zSwap_zLetterSeries_of_ne hs hs'⟩

/-- The parameter `q`, a constant of the base, is fixed by every interchange. -/
theorem C_scalarFrac_mem_zSwapFixedSubring (q : K) (r : ℕ) :
    (MvPowerSeries.C (scalarFrac K q) : AuxAlphabetSeriesFrac K (k + 1))
      ∈ zSwapFixedSubring K k r :=
  zSymmSubring_le_zSwapFixedSubring K k r (C_scalarFrac_mem_zSymmSubring q)

/-- **The values of a ring homomorphism out of `Λ` are fixed by `ŝ_m` and lie in `Z^{(k+1)}` as soon
as its values on the scalars and on the variables are.** The condition cuts out a subring, so this
is `MvPolynomial.induction_on` and nothing else.

This is how the coefficients of the closed form below are seen to be fixed by the interchange the
inductive step applies: they are values of the alphabet `(1-q)X_{r-1}`, which involves only the
letters at offsets below `r`. -/
theorem mem_zSwapFixedSubring_of_forall {A : Type*} [CommRing A]
    (Φ : Lambda A →+* AuxAlphabetSeriesFrac K (k + 1)) (r : ℕ)
    (hC : ∀ a : A, Φ (MvPolynomial.C a) ∈ zSwapFixedSubring K k r)
    (hX : ∀ i : ℕ, Φ (MvPolynomial.X i) ∈ zSwapFixedSubring K k r)
    (p : Lambda A) : Φ p ∈ zSwapFixedSubring K k r := by
  induction p using MvPolynomial.induction_on with
  | C a => exact hC a
  | add p p' hp hp' => rw [map_add]; exact Subring.add_mem _ hp hp'
  | mul_X p i hp => rw [map_mul]; exact Subring.mul_mem _ hp (hX i)

/-! ### The swapping operator on a power of the left letter of the merged alphabet -/

/-- **`HJO.Sym.isZDelta_zLetterSeries_pow_succ` at the merged letters**, which is the instance
`HJO.Sym.zSwapCoeff_succ_eq_mul_completeHomog` applies and which `HJO.Sym.xdelta_X_pow_succ` does
not cover: for `φ` the alphabet `(1-q)z_m + z_{m+1}` and every `j = n + 1 ≥ 1`, the element
`z_{m+1}·h_n[(1-q)z_m + z_{m+1}]` satisfies the defining equation of `HJO.Sym.IsZDelta` with `z_m^j`
on the right, so by `HJO.Sym.eq_of_isZDelta` it *is* `Δ_m(z_m^j)`.

The offset-`0` case is the one needing separate care: there the left letter is the
distinguished letter `y_k`, not a free variable, and `HJO.Sym.xdelta` is not the operator at all.
Nothing has to be divided — `HJO.Sym.IsZDelta` is an equation — so the proof is the ring identity
`HJO.Sym.sub_mul_mul_completeHomog_twist_add_letter` together with the two values of the interchange
on the letters it moves. -/
@[hjo "lem_cm_delta_upow"]
theorem isZDelta_zLetterSeries_pow_succ {A : Type*} [CommRing A] [Algebra ℚ A] {F : Type*}
    [FunLike F (Lambda A) (AuxAlphabetSeriesFrac K (k + 1))]
    [RingHomClass F (Lambda A) (AuxAlphabetSeriesFrac K (k + 1))] (φ : F) (q : K) (r n : ℕ)
    (hφ : ∀ j : ℕ, 0 < j → φ (powerSum A j)
      = (1 - MvPowerSeries.C (scalarFrac K q) ^ j) * zLetterSeries K k r ^ j
        + zLetterSeries K k (r + 1) ^ j) :
    IsZDelta q r (zLetterSeries K k r ^ (n + 1))
      (zLetterSeries K k (r + 1) * φ (completeHomog A n)) := by
  have hswap : zSwap K k r (zLetterSeries K k r ^ (n + 1))
      = zLetterSeries K k (r + 1) ^ (n + 1) := by
    rw [zSwap_pow_of_mem_zRing r (zLetterSeries_mem_zRing r), zSwap_zLetterSeries]
  rw [IsZDelta, zdeltaNum_apply, hswap,
    sub_mul_mul_completeHomog_twist_add_letter φ (MvPowerSeries.C (scalarFrac K q))
      (zLetterSeries K k r) (zLetterSeries K k (r + 1)) n hφ]

/-! ### The truncated twisted alphabets of the merged letters -/

variable {A : Type*} [CommRing A] [Algebra ℚ A]

omit [Algebra ℚ A] in
/-- **The alphabets `(1-q)X_{t-1} + z_t` exist.** For every homomorphism `base` of the scalars into
the lower coefficient field there is, for each `t`, a homomorphism `Λ → P°_{k+1}` extending it and
sending each power sum `p_j`, `j ≥ 1`, to `(1-q^j)(z_0^j + ⋯ + z_{t-1}^j) + z_t^j`. These are the
alphabets `HJO.Sym.zSwapCoeff_succ_eq_mul_completeHomog` is stated with:
`X_{t-1} = y_k + x_1 + ⋯ + x_{t-1}` of `HJO.Sym.truncatedAlphabet` twisted by `1-q`, plus the
untwisted next letter `z_t`, which at `t = 0` is the bare letter `y_k`. -/
theorem exists_ringHom_powerSum_eq_truncTwist_add_letter (q : K) (base : A →+* AuxFrac K k) :
    ∃ Φ : ℕ → Lambda A →+* AuxAlphabetSeriesFrac K (k + 1),
      (∀ (t : ℕ) (a : A), Φ t (MvPolynomial.C a)
          = MvPowerSeries.C (auxFracCastSucc K k (base a))) ∧
        ∀ (t j : ℕ), 0 < j → Φ t (powerSum A j)
          = (1 - MvPowerSeries.C (scalarFrac K q) ^ j)
              * (∑ s ∈ Finset.range t, zLetterSeries K k s ^ j)
            + zLetterSeries K k t ^ j := by
  refine ⟨fun t => MvPolynomial.eval₂Hom
      (((MvPowerSeries.C : AuxFrac K (k + 1) →+* AuxAlphabetSeriesFrac K (k + 1)).comp
        (auxFracCastSucc K k)).comp base)
      (fun i => (1 - MvPowerSeries.C (scalarFrac K q) ^ (i + 1))
          * (∑ s ∈ Finset.range t, zLetterSeries K k s ^ (i + 1))
        + zLetterSeries K k t ^ (i + 1)),
    fun t a => MvPolynomial.eval₂Hom_C _ _ a, fun t j hj => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [CopPower.powerSum_succ, MvPolynomial.eval₂Hom_X']

omit [Algebra ℚ A] in
/-- **The twisted truncated alphabets `(1-q)X_{t-1}` exist.** The same construction with the
untwisted letter `z_t` dropped; these are the alphabets the displayed quotient is stated
with, and `HJO.Sym.one_sub_C_scalarFrac_mul_zSwapCoeff` is that display. -/
theorem exists_ringHom_powerSum_eq_truncTwist (q : K) (base : A →+* AuxFrac K k) :
    ∃ Ψ : ℕ → Lambda A →+* AuxAlphabetSeriesFrac K (k + 1),
      (∀ (t : ℕ) (a : A), Ψ t (MvPolynomial.C a)
          = MvPowerSeries.C (auxFracCastSucc K k (base a))) ∧
        ∀ (t j : ℕ), 0 < j → Ψ t (powerSum A j)
          = (1 - MvPowerSeries.C (scalarFrac K q) ^ j)
            * ∑ s ∈ Finset.range t, zLetterSeries K k s ^ j := by
  refine ⟨fun t => MvPolynomial.eval₂Hom
      (((MvPowerSeries.C : AuxFrac K (k + 1) →+* AuxAlphabetSeriesFrac K (k + 1)).comp
        (auxFracCastSucc K k)).comp base)
      (fun i => (1 - MvPowerSeries.C (scalarFrac K q) ^ (i + 1))
        * ∑ s ∈ Finset.range t, zLetterSeries K k s ^ (i + 1)),
    fun t a => MvPolynomial.eval₂Hom_C _ _ a, fun t j hj => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [CopPower.powerSum_succ, MvPolynomial.eval₂Hom_X']

omit [Algebra ℚ A] in
/-- The scalar condition the closed form asks for, from the pinned form the existence statements
supply: a constant of the lower coefficient field is fixed by every relabelling. -/
theorem mem_zSymmSubring_of_eq_C_auxFracCastSucc {base : A →+* AuxFrac K k}
    {Φ : Lambda A →+* AuxAlphabetSeriesFrac K (k + 1)}
    (hΦ : ∀ a : A, Φ (MvPolynomial.C a) = MvPowerSeries.C (auxFracCastSucc K k (base a)))
    (a : A) : Φ (MvPolynomial.C a) ∈ zSymmSubring K k := by
  rw [hΦ a]
  exact C_auxFracCastSucc_mem_zSymmSubring _

/-! ### The inductive step -/

/-- **One step of the closed form.** With `Φ t` the alphabet `(1-q)X_{t-1} + z_t`, the element
`z_t·h_n[(1-q)X_{t-1} + z_t]` satisfies the defining equation of `HJO.Sym.IsZDelta` at the offset
`r` with the same expression at `r + 1` as its value. This is the inductive step: the
coefficients `h_{n-s}[(1-q)X_{r-1}]` involve only the letters below the offset `r`, so the
interchange passes them (`HJO.Sym.isZDelta_mul_of_zSwap_eq`), and on the remaining powers of `z_r`
it acts by `HJO.Sym.isZDelta_zLetterSeries_pow_succ` at the merged letters. -/
theorem isZDelta_zLetterSeries_mul_completeHomog {q : K}
    {Φ : ℕ → Lambda A →+* AuxAlphabetSeriesFrac K (k + 1)}
    (hΦC : ∀ a : A, Φ 0 (MvPolynomial.C a) ∈ zSymmSubring K k)
    (hΦp : ∀ (t j : ℕ), 0 < j → Φ t (powerSum A j)
      = (1 - MvPowerSeries.C (scalarFrac K q) ^ j)
          * (∑ s ∈ Finset.range t, zLetterSeries K k s ^ j) + zLetterSeries K k t ^ j)
    (r n : ℕ) :
    IsZDelta q r (zLetterSeries K k r * Φ r (completeHomog A n))
      (zLetterSeries K k (r + 1) * Φ (r + 1) (completeHomog A n)) := by
  classical
  set Q : AuxAlphabetSeriesFrac K (k + 1) := MvPowerSeries.C (scalarFrac K q) with hQdef
  set cbase : A →+* AuxAlphabetSeriesFrac K (k + 1) :=
    (Φ 0 : Lambda A →+* AuxAlphabetSeriesFrac K (k + 1)).comp MvPolynomial.C with hcbase
  -- the twisted truncated alphabet `(1-q)X_{r-1}`, whose values the interchange fixes
  set Ψ : Lambda A →+* AuxAlphabetSeriesFrac K (k + 1) := MvPolynomial.eval₂Hom cbase
    (fun i => (1 - Q ^ (i + 1)) * ∑ s ∈ Finset.range r, zLetterSeries K k s ^ (i + 1)) with hΨdef
  have hΨX : ∀ i : ℕ, Ψ (MvPolynomial.X i)
      = (1 - Q ^ (i + 1)) * ∑ s ∈ Finset.range r, zLetterSeries K k s ^ (i + 1) :=
    fun i => by rw [hΨdef, MvPolynomial.eval₂Hom_X']
  have hΨp : ∀ j : ℕ, 0 < j → Ψ (powerSum A j)
      = (1 - Q ^ j) * ∑ s ∈ Finset.range r, zLetterSeries K k s ^ j := by
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [CopPower.powerSum_succ, hΨX i]
  have hΨfix : ∀ p : Lambda A, Ψ p ∈ zSwapFixedSubring K k r := by
    refine mem_zSwapFixedSubring_of_forall Ψ r (fun a => ?_) fun i => ?_
    · rw [hΨdef, MvPolynomial.eval₂Hom_C]
      exact zSymmSubring_le_zSwapFixedSubring K k r (hΦC a)
    · rw [hΨX i]
      refine Subring.mul_mem _ (Subring.sub_mem _ (Subring.one_mem _)
        (Subring.pow_mem _ (C_scalarFrac_mem_zSwapFixedSubring q r) _)) ?_
      refine Subring.sum_mem _ fun s hs => Subring.pow_mem _ ?_ _
      have hsr : s < r := Finset.mem_range.1 hs
      exact zLetterSeries_mem_zSwapFixedSubring (by omega) (by omega)
  -- the plain letter `z_r`
  set ν : Lambda A →+* AuxAlphabetSeriesFrac K (k + 1) := MvPolynomial.eval₂Hom cbase
    (fun i => zLetterSeries K k r ^ (i + 1)) with hνdef
  have hνX : ∀ i : ℕ, ν (MvPolynomial.X i) = zLetterSeries K k r ^ (i + 1) :=
    fun i => by rw [hνdef, MvPolynomial.eval₂Hom_X']
  have hνp : ∀ j : ℕ, 0 < j → ν (powerSum A j) = zLetterSeries K k r ^ j := by
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [CopPower.powerSum_succ, hνX i]
  have hνh : ∀ s : ℕ, ν (completeHomog A s) = zLetterSeries K k r ^ s :=
    completeHomog_single_letter ν _ hνp
  -- the two-letter alphabet `(1-q)z_r + z_{r+1}` of `HJO.Sym.isZDelta_zLetterSeries_pow_succ`
  set φ : Lambda A →+* AuxAlphabetSeriesFrac K (k + 1) := MvPolynomial.eval₂Hom cbase
    (fun i => (1 - Q ^ (i + 1)) * zLetterSeries K k r ^ (i + 1)
      + zLetterSeries K k (r + 1) ^ (i + 1)) with hφdef
  have hφX : ∀ i : ℕ, φ (MvPolynomial.X i)
      = (1 - Q ^ (i + 1)) * zLetterSeries K k r ^ (i + 1)
        + zLetterSeries K k (r + 1) ^ (i + 1) :=
    fun i => by rw [hφdef, MvPolynomial.eval₂Hom_X']
  have hφp : ∀ j : ℕ, 0 < j → φ (powerSum A j)
      = (1 - Q ^ j) * zLetterSeries K k r ^ j + zLetterSeries K k (r + 1) ^ j := by
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [CopPower.powerSum_succ, hφX i]
  -- the two alphabet decompositions
  have haddν : ∀ j : ℕ, 0 < j → Φ r (powerSum A j) = Ψ (powerSum A j) + ν (powerSum A j) := by
    intro j hj
    rw [hΦp r j hj, hΨp j hj, hνp j hj]
  have haddφ : ∀ j : ℕ, 0 < j →
      Φ (r + 1) (powerSum A j) = Ψ (powerSum A j) + φ (powerSum A j) := by
    intro j hj
    rw [hΦp (r + 1) j hj, hΨp j hj, hφp j hj, Finset.sum_range_succ]
    ring
  have hΦrh : Φ r (completeHomog A n)
      = ∑ s ∈ Finset.range (n + 1), Ψ (completeHomog A (n - s)) * ν (completeHomog A s) :=
    completeHomog_add_alphabet Ψ ν (Φ r) haddν n
  have hΦr1h : Φ (r + 1) (completeHomog A n)
      = ∑ s ∈ Finset.range (n + 1), Ψ (completeHomog A (n - s)) * φ (completeHomog A s) :=
    completeHomog_add_alphabet Ψ φ (Φ (r + 1)) haddφ n
  have hL : (∑ s ∈ Finset.range (n + 1),
        Ψ (completeHomog A (n - s)) * zLetterSeries K k r ^ (s + 1))
      = zLetterSeries K k r * Φ r (completeHomog A n) := by
    rw [hΦrh, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hνh s, pow_succ]
    ring
  have hR : (∑ s ∈ Finset.range (n + 1),
        Ψ (completeHomog A (n - s)) * (zLetterSeries K k (r + 1) * φ (completeHomog A s)))
      = zLetterSeries K k (r + 1) * Φ (r + 1) (completeHomog A n) := by
    rw [hΦr1h, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [← hL, ← hR]
  refine isZDelta_sum (fun s _ => mul_mem_zRing (hΨfix _).1
      (pow_mem_zRing (zLetterSeries_mem_zRing r) _)) fun s _ => ?_
  exact isZDelta_mul_of_zSwap_eq (pow_mem_zRing (zLetterSeries_mem_zRing r) _) (hΨfix _).1
    (hΨfix _).2 (isZDelta_zLetterSeries_pow_succ φ q r s hφp)

/-! ### The closed form -/

/-- **The closed form of the swapping coefficients.** For `i = n + 1 ≥ 1` and every `t ≥ 0`,

`f_{i,t} = z_t·h_{i-1}[(1-q)X_{t-1} + z_t]`,

with `X_{t-1} = y_k + x_1 + ⋯ + x_{t-1}` of `HJO.Sym.truncatedAlphabet` and `z_t` the next letter of
the merged alphabet — `y_k` itself at `t = 0`. This is the form derived from the displayed quotient
in the proof of `HJO.Sym.zSwapCoeff_succ_eq_mul_completeHomog`, which inducts on it;
`HJO.Sym.one_sub_C_scalarFrac_mul_zSwapCoeff` is the displayed quotient itself.

The induction is `HJO.Sym.eq_zSwapCoeff`: at `t = 0` the alphabet is the single letter `y_k`, so the
value is `y_k^i`, and the step is `HJO.Sym.isZDelta_zLetterSeries_mul_completeHomog`. Such a family
of alphabets exists, by `HJO.Sym.exists_ringHom_powerSum_eq_truncTwist_add_letter`. -/
@[hjo "lem_cm_fir_closed"]
theorem zSwapCoeff_succ_eq_mul_completeHomog {q : K}
    {Φ : ℕ → Lambda A →+* AuxAlphabetSeriesFrac K (k + 1)}
    (hΦC : ∀ a : A, Φ 0 (MvPolynomial.C a) ∈ zSymmSubring K k)
    (hΦp : ∀ (t j : ℕ), 0 < j → Φ t (powerSum A j)
      = (1 - MvPowerSeries.C (scalarFrac K q) ^ j)
          * (∑ s ∈ Finset.range t, zLetterSeries K k s ^ j) + zLetterSeries K k t ^ j)
    (n t : ℕ) :
    zSwapCoeff K k q (n + 1) t = zLetterSeries K k t * Φ t (completeHomog A n) := by
  refine (eq_zSwapCoeff (g := fun t => zLetterSeries K k t * Φ t (completeHomog A n)) q (n + 1)
    ?_ (fun r => isZDelta_zLetterSeries_mul_completeHomog hΦC hΦp r n) t).symm
  have h0p : ∀ j : ℕ, 0 < j → Φ 0 (powerSum A j) = zLetterSeries K k 0 ^ j := by
    intro j hj
    rw [hΦp 0 j hj, Finset.range_zero, Finset.sum_empty, mul_zero, zero_add]
  change zLetterSeries K k 0 * Φ 0 (completeHomog A n)
    = MvPowerSeries.C (yFrac K (Fin.last k)) ^ (n + 1)
  rw [completeHomog_single_letter (Φ 0) _ h0p n, ← pow_succ', zLetterSeries_zero]

/-! ### The displayed quotient -/

/-- **The closed form as displayed.** With `Ψ t` the twisted truncated alphabet
`(1-q)X_{t-1}` — so `Ψ (t+1)` is `(1-q)X_t` — for every `i = n + 1 ≥ 1` and every `t ≥ 0`

`(1-q)·f_{i,t} = h_i[(1-q)X_t] - h_i[(1-q)X_{t-1}]`,

which is the `f_{i,t} = (h_i[(1-q)X_t] - h_i[(1-q)X_{t-1}])/(1-q)` with the division
written as a product. The division itself is *not* performed: `1-q` is not a unit of `P°_{k+1}` for
a general base, and the proof of the identity never divides either — it computes the
numerator and observes that `1-q` factors out. So this is the same content, and
`HJO.Sym.zSwapCoeff_succ_eq_mul_completeHomog` is the quotient itself, in the form
`z_t·h_{i-1}[(1-q)X_{t-1} + z_t]` derived from the display before inducting.

The step is `HJO.Sym.completeHomog_add_alphabet` at `(1-q)X_t = (1-q)X_{t-1} + (1-q)z_t` together
with `HJO.Sym.completeHomog_dilate_letter` for the one-letter factor, which contributes `1` in
degree `0` and `(1-q)z_t^s` above it; peeling the degree-`0` term is what cancels
`h_i[(1-q)X_{t-1}]`. -/
@[hjo "lem_cm_fir_closed"]
theorem one_sub_C_scalarFrac_mul_zSwapCoeff {q : K}
    {Φ Ψ : ℕ → Lambda A →+* AuxAlphabetSeriesFrac K (k + 1)}
    (hΦC : ∀ a : A, Φ 0 (MvPolynomial.C a) ∈ zSymmSubring K k)
    (hΦp : ∀ (t j : ℕ), 0 < j → Φ t (powerSum A j)
      = (1 - MvPowerSeries.C (scalarFrac K q) ^ j)
          * (∑ s ∈ Finset.range t, zLetterSeries K k s ^ j) + zLetterSeries K k t ^ j)
    (hΨp : ∀ (t j : ℕ), 0 < j → Ψ t (powerSum A j)
      = (1 - MvPowerSeries.C (scalarFrac K q) ^ j)
          * ∑ s ∈ Finset.range t, zLetterSeries K k s ^ j)
    (n t : ℕ) :
    (1 - MvPowerSeries.C (scalarFrac K q)) * zSwapCoeff K k q (n + 1) t
      = Ψ (t + 1) (completeHomog A (n + 1)) - Ψ t (completeHomog A (n + 1)) := by
  classical
  set Q : AuxAlphabetSeriesFrac K (k + 1) := MvPowerSeries.C (scalarFrac K q) with hQdef
  set cbase : A →+* AuxAlphabetSeriesFrac K (k + 1) :=
    (Φ 0 : Lambda A →+* AuxAlphabetSeriesFrac K (k + 1)).comp MvPolynomial.C with hcbase
  -- the plain letter `z_t`
  set ν : Lambda A →+* AuxAlphabetSeriesFrac K (k + 1) := MvPolynomial.eval₂Hom cbase
    (fun i => zLetterSeries K k t ^ (i + 1)) with hνdef
  have hνX : ∀ i : ℕ, ν (MvPolynomial.X i) = zLetterSeries K k t ^ (i + 1) :=
    fun i => by rw [hνdef, MvPolynomial.eval₂Hom_X']
  have hνp : ∀ j : ℕ, 0 < j → ν (powerSum A j) = zLetterSeries K k t ^ j := by
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [CopPower.powerSum_succ, hνX i]
  have hνh : ∀ s : ℕ, ν (completeHomog A s) = zLetterSeries K k t ^ s :=
    completeHomog_single_letter ν _ hνp
  -- the twisted letter `(1-q)z_t`
  set B : Lambda A →+* AuxAlphabetSeriesFrac K (k + 1) := MvPolynomial.eval₂Hom cbase
    (fun i => (1 - Q ^ (i + 1)) * zLetterSeries K k t ^ (i + 1)) with hBdef
  have hBX : ∀ i : ℕ, B (MvPolynomial.X i)
      = (1 - Q ^ (i + 1)) * zLetterSeries K k t ^ (i + 1) :=
    fun i => by rw [hBdef, MvPolynomial.eval₂Hom_X']
  have hBp : ∀ j : ℕ, 0 < j → B (powerSum A j) = (1 - Q ^ j) * zLetterSeries K k t ^ j := by
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [CopPower.powerSum_succ, hBX i]
  have hBh : ∀ b : ℕ, 0 < b → B (completeHomog A b) = (1 - Q) * zLetterSeries K k t ^ b :=
    fun b hb => completeHomog_dilate_letter B _ _ hBp hb
  -- the two alphabet decompositions
  have haddν : ∀ j : ℕ, 0 < j → Φ t (powerSum A j) = Ψ t (powerSum A j) + ν (powerSum A j) := by
    intro j hj
    rw [hΦp t j hj, hΨp t j hj, hνp j hj]
  have haddB : ∀ j : ℕ, 0 < j →
      Ψ (t + 1) (powerSum A j) = Ψ t (powerSum A j) + B (powerSum A j) := by
    intro j hj
    rw [hΨp (t + 1) j hj, hΨp t j hj, hBp j hj, Finset.sum_range_succ]
    ring
  have hΦth : Φ t (completeHomog A n)
      = ∑ s ∈ Finset.range (n + 1), Ψ t (completeHomog A (n - s)) * ν (completeHomog A s) :=
    completeHomog_add_alphabet (Ψ t) ν (Φ t) haddν n
  have hΨ1 : Ψ (t + 1) (completeHomog A (n + 1))
      = ∑ s ∈ Finset.range (n + 1 + 1),
          Ψ t (completeHomog A (n + 1 - s)) * B (completeHomog A s) :=
    completeHomog_add_alphabet (Ψ t) B (Ψ (t + 1)) haddB (n + 1)
  have hkey : (∑ s ∈ Finset.range (n + 1),
        Ψ t (completeHomog A (n + 1 - (s + 1))) * B (completeHomog A (s + 1)))
      = (1 - Q) * (zLetterSeries K k t * Φ t (completeHomog A n)) := by
    rw [hΦth]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Nat.succ_sub_succ, hBh (s + 1) (Nat.succ_pos s), hνh s, pow_succ]
    ring
  rw [zSwapCoeff_succ_eq_mul_completeHomog hΦC hΦp n t, hΨ1, Finset.sum_range_succ',
    Nat.sub_zero, CopPower.completeHomog_zero, map_one, mul_one, hkey]
  ring

end HJO.Sym
