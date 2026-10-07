/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.PDelta
public import HJO.DyckWordMonomial
public meta import HJO.Attr

/-! # The weight of a run, and the monomial of a labelling

A run of length `l` inside the two-letter support of a labelling contributes to the characteristic
series a single term `a_m(l, ε)`, where `ε` records which of the two letters `m`, `m + 1` the run
starts with: the letters alternate along the run, so the whole run is determined by that one bit,
and its contribution is a power of `q` times a monomial in the two merged variables. This file
defines that weight, the monomial `z^{(k)}_w` of a whole labelling, and proves the two identities
the swapping proposition needs: `Δ_m` carries the weight of a run starting at `m` to the weight of
the same run starting at `m + 1`, and the sum of the two weights is `ŝ_m`-invariant.

## Main definitions

* `HJO.Sym.runWeight`: `a_m(l, ε)`, as a monomial in three elements of a commutative ring.
* `HJO.Sym.runWeightZvar`: the same at the merged variables of `P_k`, the run weight
  `a_m(l, ε)`.
* `HJO.Sym.zmon`: `z^{(k)}_w`, the monomial of a labelling.

## Main results

* `HJO.Sym.runWeight_two_mul`, `HJO.Sym.runWeight_two_mul_add_one`: the four-line table of the
  paper, the weight written out separately for even and odd run lengths.
* `HJO.Sym.pdelta_runWeight`: `Δ_m(a_m(l, 0)) = a_m(l, 1)`.
* `HJO.Sym.pswap_runWeight_add`: `ŝ_m(a_m(l, 0) + a_m(l, 1)) = a_m(l, 0) + a_m(l, 1)`.

## Implementation notes

*`runWeight` is stated for three elements of an arbitrary commutative ring.* The weight
`a_m(l, ε)`, Carlsson and Mellit's `a(l, c)`, is this at `q` the parameter and at the two merged
variables `z^{(k)}_m`, `z^{(k)}_{m+1}` of `P_k`, which is `HJO.Sym.runWeightZvar`; the two
identities below are needed inside `P°_k`, where the variables are `y_m` and `y_{m+1}`, and stating
the weight once for a general ring is what lets one definition serve both without a second copy. The
image of the `P_k` instance under the containment `HJO.Sym.auxToFrac` is
`HJO.Sym.auxToFrac_runWeightZvar`.

*The bit `ε` is a `Bool`*, the index `ε ∈ {0, 1}` of `a_m(l, ε)`: `false` is `0`, the run starting
with the letter `m`, and `true` is its `1`.

*The ceilings and floors are `ℕ` division.* `⌊l/2⌋` is `l / 2`, `⌈l/2⌉` is `(l + 1) / 2`,
`⌊(l-1)/2⌋` is `(l - 1) / 2` and `⌈(l-1)/2⌉` is `l / 2`; the last is an identity of natural numbers
for `l ≥ 1`, which is the range of run lengths, and the truncated subtraction in the third is
harmless because at `l = 0` both readings give `0`. No lemma below is applied at `l = 0`.

## References

This file formalises the definitions `HJO.Sym.runWeight` and `HJO.Sym.zmon` and the lemmas
`HJO.Sym.pdelta_runWeight` and `HJO.Sym.pswap_runWeight_add`, on swapping operators; E. Carlsson and
A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697,
Section 4.
-/

@[expose] public section

namespace HJO.Sym

/-! ### The weight of a run -/

/-- **The weight of a run** of length `l` whose first letter is `m` (`ε = false`) or `m + 1`
(`ε = true`), as the monomial

`a_m(l, 0) = q^⌊(l-1)/2⌋ u^⌈l/2⌉ v^⌊l/2⌋`,  `a_m(l, 1) = q^⌈(l-1)/2⌉ u^⌊l/2⌋ v^⌈l/2⌉`,

in three elements `q`, `u`, `v` of a commutative ring. The weight `a_m(l, ε) ∈ P_k` is this at
`u = z^{(k)}_m` and `v = z^{(k)}_{m+1}`, which is `HJO.Sym.runWeightZvar`; the level is suppressed
in the notation and appears here only through those two variables. -/
@[hjo "def_cm_runweight"]
def runWeight {A : Type*} [CommRing A] (q u v : A) (l : ℕ) : Bool → A
  | false => q ^ ((l - 1) / 2) * u ^ ((l + 1) / 2) * v ^ (l / 2)
  | true => q ^ (l / 2) * u ^ (l / 2) * v ^ ((l + 1) / 2)

variable {A : Type*} [CommRing A] (q u v : A)

/-- **The weight of a run of even length**, the first two lines of the paper's table: for
`l = 2l'` with `l' ≥ 1` the two weights differ only by one factor of `q`, and both are symmetric in
the two variables. -/
theorem runWeight_two_mul {l' : ℕ} (hl' : 1 ≤ l') :
    runWeight q u v (2 * l') false = q ^ (l' - 1) * (u * v) ^ l' ∧
      runWeight q u v (2 * l') true = q ^ l' * (u * v) ^ l' := by
  have h1 : (2 * l' - 1) / 2 = l' - 1 := by omega
  have h2 : (2 * l' + 1) / 2 = l' := by omega
  have h3 : 2 * l' / 2 = l' := by omega
  refine ⟨?_, ?_⟩ <;> simp only [runWeight, h1, h2, h3, mul_pow] <;> ring

/-- **The weight of a run of odd length**, the last two lines of the paper's table: for
`l = 2l' + 1` the two weights share the symmetric factor `q^{l'}(uv)^{l'}` and differ in the single
remaining variable, which is exactly what makes `Δ_m` carry one to the other. -/
theorem runWeight_two_mul_add_one (l' : ℕ) :
    runWeight q u v (2 * l' + 1) false = q ^ l' * (u * v) ^ l' * u ∧
      runWeight q u v (2 * l' + 1) true = q ^ l' * (u * v) ^ l' * v := by
  have h1 : (2 * l' + 1 - 1) / 2 = l' := by omega
  have h2 : (2 * l' + 1 + 1) / 2 = l' + 1 := by omega
  have h3 : (2 * l' + 1) / 2 = l' := by omega
  refine ⟨?_, ?_⟩ <;> simp only [runWeight, h1, h2, h3, mul_pow] <;> ring

/-- **The two weights of a run sum to a symmetric expression**: interchanging the two variables
leaves `a_m(l, 0) + a_m(l, 1)` alone. For an even length each weight is separately symmetric; for an
odd one the interchange swaps the two weights. -/
theorem runWeight_add_comm (l : ℕ) :
    runWeight q v u l false + runWeight q v u l true
      = runWeight q u v l false + runWeight q u v l true := by
  rcases Nat.even_or_odd l with ⟨l', rfl⟩ | ⟨l', rfl⟩
  · rcases Nat.eq_zero_or_pos l' with rfl | hl'
    · simp [runWeight]
    · obtain ⟨e0, e1⟩ := runWeight_two_mul q u v (l' := l') hl'
      obtain ⟨f0, f1⟩ := runWeight_two_mul q v u (l' := l') hl'
      rw [show l' + l' = 2 * l' by ring] at *
      rw [e0, e1, f0, f1]
      ring
  · obtain ⟨e0, e1⟩ := runWeight_two_mul_add_one q u v l'
    obtain ⟨f0, f1⟩ := runWeight_two_mul_add_one q v u l'
    rw [show 2 * l' + 1 = 2 * l' + 1 from rfl] at *
    rw [e0, e1, f0, f1]
    ring

/-! ### The monomial of a labelling -/

/-- **The full labelling monomial** `z^{(k)}_w = ∏_i z^{(k)}_{w_i} ∈ P_k`: the product of the merged
variables named by the letters of the labelling `w`, taken with multiplicity. At the level `0` the
merged variables are the letters of the alphabet and this is the monomial `x_w` of
`HJO.Sym.wordMonomial`. -/
@[hjo "def_cm_zmon"]
noncomputable def zmon (K : Type*) [CommRing K] (k : ℕ) {N : ℕ} (w : Fin N → ℕ) :
    AuxAlphabetSeries K k :=
  ∏ i : Fin N, zvar K k (w i)

/-- At the level `0` the labelling monomial is the product of the letters of the word, which is the
formula defining `HJO.Sym.wordMonomial`: every merged variable is then a letter of the alphabet,
with no shift. The two are not the same declaration because `AuxAlphabetSeries K 0` has coefficients
`MvPolynomial (Fin 0) K` rather than `K`, the identification of the two being the canonical
isomorphism of those coefficient rings. -/
theorem zmon_zero (K : Type*) [CommRing K] {N : ℕ} (w : Fin N → ℕ) :
    zmon K 0 w = ∏ i : Fin N, MvPowerSeries.X (w i) :=
  Finset.prod_congr rfl fun i _ => zvar_zero (w i)

/-! ### The weight at the merged variables -/

variable {K : Type*} [CommRing K]

/-- A scalar of the base read inside `P_k`, the constant series with constant coefficient: this is
how the parameter `q` of the paper enters the weight of a run. -/
noncomputable def scalarSeries (K : Type*) [CommRing K] (k : ℕ) (a : K) : AuxAlphabetSeries K k :=
  MvPowerSeries.C (MvPolynomial.C a)

/-- The containment `P_k ⊆ P°_k` on a constant series: it moves the coefficient by the localization
map. -/
theorem auxToFrac_C (k : ℕ) (c : MvPolynomial (Fin k) K) :
    auxToFrac K k (MvPowerSeries.C c) = MvPowerSeries.C (algebraMap _ (AuxFrac K k) c) :=
  MvPowerSeries.ext fun e => by
    rw [coeff_auxToFrac]
    simp only [MvPowerSeries.coeff_C]
    split
    · rfl
    · exact map_zero _

@[simp]
theorem auxToFrac_scalarSeries (k : ℕ) (a : K) :
    auxToFrac K k (scalarSeries K k a) = MvPowerSeries.C (scalarFrac K a) :=
  auxToFrac_C k _

/-- Below the level, the containment `P_k ⊆ P°_k` carries a merged variable to the constant series
at the corresponding auxiliary variable of the fraction field. -/
theorem auxToFrac_zvar_of_lt {k m : ℕ} (h : m < k) :
    auxToFrac K k (zvar K k m) = MvPowerSeries.C (yFrac K ⟨m, h⟩) := by
  rw [zvar_of_lt h, auxToFrac_C]
  rfl

/-- **The weight `a_m(l, ε) ∈ P_k`**: the weight of a run at the two merged variables
`z^{(k)}_m` and `z^{(k)}_{m+1}` of the level `k`, with the parameter `q` read as a constant series.
Labels are indexed from `0`, so this is the one-based `a_{m+1}(l, ε)`. -/
@[hjo "def_cm_runweight"]
noncomputable abbrev runWeightZvar (q : K) (k m l : ℕ) (ε : Bool) : AuxAlphabetSeries K k :=
  runWeight (scalarSeries K k q) (zvar K k m) (zvar K k (m + 1)) l ε

/-- The weight of a run, pushed from `P_k` into `P°_k` through the containment: below the level the
two merged variables become the two auxiliary variables of the fraction field, which is the form the
swapping operator acts on. -/
theorem auxToFrac_runWeightZvar (q : K) {k : ℕ} {i j : Fin k} (hj : (j : ℕ) = (i : ℕ) + 1)
    (l : ℕ) (ε : Bool) :
    auxToFrac K k (runWeightZvar q k (i : ℕ) l ε)
      = runWeight (MvPowerSeries.C (scalarFrac K q)) (MvPowerSeries.C (yFrac K i))
          (MvPowerSeries.C (yFrac K j)) l ε := by
  have hi : (i : ℕ) < k := i.isLt
  have hj' : (i : ℕ) + 1 < k := hj ▸ j.isLt
  have hzi : auxToFrac K k (zvar K k (i : ℕ)) = MvPowerSeries.C (yFrac K i) := by
    rw [auxToFrac_zvar_of_lt hi]
  have hje : (⟨(i : ℕ) + 1, hj'⟩ : Fin k) = j := Fin.ext hj.symm
  have hzj : auxToFrac K k (zvar K k ((i : ℕ) + 1)) = MvPowerSeries.C (yFrac K j) := by
    rw [auxToFrac_zvar_of_lt hj', hje]
  cases ε <;>
    simp only [runWeight, map_mul, map_pow, auxToFrac_scalarSeries, hzi, hzj]

/-! ### The swapping operator on the weight of a run -/

/-- **The swapping operator flips the weight of a run**: `Δ_m(a_m(l, 0)) = a_m(l, 1)`. For an even
length the weight is `ŝ_m`-invariant and `Δ_m` multiplies it by `q`, which is exactly the difference
between the two weights; for an odd length the symmetric factor `q^{l'}(y_m y_{m+1})^{l'}` comes out
of `Δ_m` and `Δ_m(y_m) = y_{m+1}` finishes. -/
@[hjo "lem_cm_runweight_delta"]
theorem pdelta_runWeight [IsDomain K] (q : K) {k : ℕ} {i j : Fin k} (hij : i ≠ j) {l : ℕ}
    (hl : 1 ≤ l) :
    pdelta q i j (runWeight (MvPowerSeries.C (scalarFrac K q)) (MvPowerSeries.C (yFrac K i))
        (MvPowerSeries.C (yFrac K j)) l false)
      = runWeight (MvPowerSeries.C (scalarFrac K q)) (MvPowerSeries.C (yFrac K i))
          (MvPowerSeries.C (yFrac K j)) l true := by
  set Q : AuxAlphabetSeriesFrac K k := MvPowerSeries.C (scalarFrac K q) with hQ
  set U : AuxAlphabetSeriesFrac K k := MvPowerSeries.C (yFrac K i) with hU
  set V : AuxAlphabetSeriesFrac K k := MvPowerSeries.C (yFrac K j) with hV
  have hQs : pswap K i j Q = Q := by rw [hQ]; exact pswap_C_scalarFrac q
  have hUV : pswap K i j (U * V) = U * V := by
    rw [map_mul, hU, hV, pswap_C_yFrac_left, pswap_C_yFrac_right, mul_comm]
  rcases Nat.even_or_odd l with ⟨l', rfl⟩ | ⟨l', rfl⟩
  · have hl' : 1 ≤ l' := by omega
    obtain ⟨e0, e1⟩ := runWeight_two_mul Q U V (l' := l') hl'
    rw [show l' + l' = 2 * l' by ring] at *
    rw [e0, e1]
    have hinv : pswap K i j (Q ^ (l' - 1) * (U * V) ^ l') = Q ^ (l' - 1) * (U * V) ^ l' := by
      rw [map_mul, map_pow, map_pow, hQs, hUV]
    rw [pdelta_of_pswap_eq hij hinv, hQ]
    rw [show Q ^ l' = Q * Q ^ (l' - 1) by rw [← pow_succ']; congr 1; omega]
    ring
  · obtain ⟨e0, e1⟩ := runWeight_two_mul_add_one Q U V l'
    rw [e0, e1]
    have hinv : pswap K i j (Q ^ l' * (U * V) ^ l') = Q ^ l' * (U * V) ^ l' := by
      rw [map_mul, map_pow, map_pow, hQs, hUV]
    rw [pdelta_mul_of_pswap_eq hinv, hU, hV, pdelta_C_yFrac hij]

/-- **The two weights of a run sum to an invariant**: `ŝ_m` fixes `a_m(l, 0) + a_m(l, 1)`. For an
even length each summand is separately fixed; for an odd one the interchange swaps them. -/
@[hjo "lem_cm_runweight_sum_symmetric"]
theorem pswap_runWeight_add (q : K) {k : ℕ} (i j : Fin k) (l : ℕ) :
    pswap K i j (runWeight (MvPowerSeries.C (scalarFrac K q)) (MvPowerSeries.C (yFrac K i))
          (MvPowerSeries.C (yFrac K j)) l false
        + runWeight (MvPowerSeries.C (scalarFrac K q)) (MvPowerSeries.C (yFrac K i))
          (MvPowerSeries.C (yFrac K j)) l true)
      = runWeight (MvPowerSeries.C (scalarFrac K q)) (MvPowerSeries.C (yFrac K i))
          (MvPowerSeries.C (yFrac K j)) l false
        + runWeight (MvPowerSeries.C (scalarFrac K q)) (MvPowerSeries.C (yFrac K i))
          (MvPowerSeries.C (yFrac K j)) l true := by
  have hkey : ∀ ε : Bool,
      pswap K i j (runWeight (MvPowerSeries.C (scalarFrac K q)) (MvPowerSeries.C (yFrac K i))
          (MvPowerSeries.C (yFrac K j)) l ε)
        = runWeight (MvPowerSeries.C (scalarFrac K q)) (MvPowerSeries.C (yFrac K j))
            (MvPowerSeries.C (yFrac K i)) l ε := fun ε => by
    cases ε <;>
      simp only [runWeight, map_mul, map_pow, pswap_C_scalarFrac, pswap_C_yFrac_left,
        pswap_C_yFrac_right]
  rw [map_add, hkey, hkey]
  exact runWeight_add_comm _ _ _ l

end HJO.Sym
