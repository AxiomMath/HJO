/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.ChiPrime
public import HJO.CarlssonMellit.ZSubring
public meta import HJO.Attr

/-! # The characteristic series is alphabet-graded

One lemma, `HJO.Dyck.auxToFrac_unnormalisedCharPart_mem_zGraded`: the unnormalised characteristic
series `χ'_σ(π)` of `HJO.Dyck.unnormalisedCharSeries` lies in `⨁_{d=0}^{N}Z^{(k)}_d`, the sum of the
graded pieces of the *merged alphabet* `y_k, x_1, x_2, …` of `HJO.Sym.zGraded` in degrees at most
the number `N` of positions of the path.

The decomposition is the grouping of the defining sum. A labelling `w` of the `N` positions
contributes the monomial `z^{(k)}_w`, a product of `N` merged variables, each of which is one of the
lower auxiliary variables `y_1, …, y_{k-1}`, contributing nothing to the merged alphabet, or one of
`y_k, x_1, x_2, …`. Writing `d(w)` for the number of factors of the second kind, so that
`0 ≤ d(w) ≤ N`, the part of `χ'_σ(π)` collecting the labellings with `d(w) = d` is a formal
combination over the lower field of monomials of degree exactly `d` in the merged alphabet, and the
`N + 1` parts sum back to `χ'_σ(π)`. That the sum is *direct* is
`HJO.Sym.eq_zero_of_sum_eq_zero_of_mem_zGraded`, so the family exhibited here is the unique one.

The level is written `k + 1`, as `HJO.Sym.zGraded` is: the level `k ≥ 1` is `k + 1` here,
its coefficient field `𝕂(y_1, …, y_{k-1})` is `HJO.Sym.AuxFrac K k` included by
`HJO.Sym.auxFracCastSucc`, and its distinguished merged letter `y_k` is
`HJO.Sym.yFrac K (Fin.last k)`. A letter `j` of a labelling is below the level when `j < k`, is the
distinguished letter when `j = k`, and is a letter `x_{j-k}` of the alphabet when `k < j`; so the
merged degree `d(w)` counts the positions whose letter is at least `k`, and it splits as the number
of positions carrying the distinguished letter plus the total degree of `HJO.Sym.zmonExponent` in
the alphabet.

## Main definitions

* `HJO.Dyck.mergedDegree`: `d(w)`, the number of positions whose letter lies in the merged alphabet.
* `HJO.Sym.lastAuxDegree`: the number of positions carrying the distinguished merged letter `y_k`,
  which is the exponent of `y_k` in the labelling monomial.
* `HJO.Dyck.unnormalisedCharPart`: the part of `χ'_σ(π)` of merged degree `d`.

## Main results

* `HJO.Dyck.auxToFrac_unnormalisedCharPart_mem_zGraded`: the part of merged degree `d` lies in
  `Z^{(k)}_d`.
* `HJO.Dyck.sum_unnormalisedCharPart`, `HJO.Dyck.sum_auxToFrac_unnormalisedCharPart`: the parts of
  merged degrees `0, …, N` sum to `χ'_σ(π)`, in `P_{k+1}` and in `P°_{k+1}`.
* `HJO.Dyck.auxToFrac_unnormalisedCharSeries_mem_zRing`: consequently `χ'_σ(π)` lies in `Z^{(k)}`.
* `HJO.Dyck.mergedDegree_eq_lastAuxDegree_add_degree`: the merged degree of a labelling splits into
  the exponent of the distinguished letter and the alphabet degree of the labelling monomial.
* `HJO.Sym.zmonCoeff_succ`: the labelling monomial's coefficient is a power of the distinguished
  auxiliary variable times an element of the lower polynomial ring.

## Implementation notes

*The statement is the family, not merely the membership in `Z^{(k)}`.* The statement as usually
given asserts membership in a direct sum, so the content is the existence of the graded parts
together with their degrees and their sum; `auxToFrac_unnormalisedCharPart_mem_zGraded` and
`sum_auxToFrac_unnormalisedCharPart` are those two halves, and
`auxToFrac_unnormalisedCharSeries_mem_zRing` is the packaged corollary in the set `HJO.Sym.zRing`.
The directness is not reproved here: it is a property of the pieces,
`HJO.Sym.eq_zero_of_sum_eq_zero_of_mem_zGraded`, and applies verbatim to this family.

*`χ'_σ(π)` lives in `P_{k+1}` and `Z^{(k+1)}_d` in `P°_{k+1}`*, so the membership is asserted of
`HJO.Sym.auxToFrac K (k+1) (χ'_σ(π))`. That inclusion acts on each coefficient separately, so it
neither creates nor destroys merged degree; the parts themselves are defined in `P_{k+1}`, where the
grouping of a sum of monomials takes place.

*The exponent of the distinguished letter is never a truncated subtraction.* `HJO.Sym.zGraded` asks
for a witness `b` with `b + |α| = d`, and the witness supplied is `lastAuxDegree k w`, the number of
positions of `w` carrying the letter `k`. All the labellings contributing to one coefficient of one
part share that number, because they share both `HJO.Sym.zmonExponent`, hence `|α|`, and the merged
degree `d`; `mergedDegree_eq_lastAuxDegree_add_degree` is what identifies it with `b`.

*No hypothesis on the path, on `σ` or on `N ≥ k`.* The statement as usually given has `N ≥ k`,
`π ∈ 𝔻_{k,N}`
and a `σ` of pairwise distinct positive integers; the proof spends none of the three, and they are
absent here. What drives it is that every summand of `χ'_σ(π)` is a product of `N` merged variables,
so at most `N` of its factors lie in the merged alphabet, whatever the path and the prescription
are. As for `HJO.Dyck.unnormalisedCharSeries` itself, those conditions are hypotheses of the lemmas
that consume `χ'_σ(π)`, not of this one.

*The parts vanish above `N` and the sum is over `Finset.range (N + 1)`.* This is where the degree
bound `d ≤ N` of the `⨁_{d=0}^{N}` sits: `unnormalisedCharPart_eq_zero` records that a
merged degree exceeding `N` is unreachable, `HJO.Dyck.mergedDegree_le` being the count of positions.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 4. The lemma uses `HJO.Dyck.IsPartialDyck`, `HJO.Dyck.unnormalisedCharSeries`,
`HJO.Sym.zGraded`, `HJO.Sym.zRing` and `HJO.Sym.eq_zero_of_sum_eq_zero_of_mem_zGraded`. The alphabet
grading is an apparatus of this library rather than of Carlsson and Mellit, who work over a field of
rational functions throughout. Consumed by
`HJO.Dyck.auxToFrac_unnormalisedCharSeries_transposeTuple` and
`HJO.Dyck.zSwap_auxToFrac_unnormalisedCharSeries`, which need `χ'_σ(π)` to lie where the operators
of `HJO.Sym.zPerm` and `HJO.Sym.IsZDelta` are defined. -/

@[expose] public section

open Finset

namespace HJO.Sym

variable {K : Type*} [CommRing K] {N k : ℕ}

/-! ### The distinguished letter in the labelling monomial's coefficient -/

/-- The number of positions of `w` carrying the letter `k`, which at the level `k + 1` is the one
letter below the level that belongs to the merged alphabet: at the level `k + 1` the letters `j < k`
name the lower auxiliary variables `y_1, …, y_k`, the letter `k` names the distinguished auxiliary
variable `y_{k+1}`, and the letters `k < j` name the letters `x_{j-k}` of the alphabet. So this is
the exponent of `y_{k+1}` in the coefficient `HJO.Sym.zmonCoeff K (k+1) w` of the labelling
monomial. -/
def lastAuxDegree (k : ℕ) {N : ℕ} (w : Fin N → ℕ) : ℕ :=
  #{i : Fin N | w i = k}

/-- **The labelling monomial's coefficient splits off the distinguished auxiliary variable**: at the
level `k + 1` the coefficient `HJO.Sym.zmonCoeff K (k+1) w` in `𝕜[y_1, …, y_{k+1}]` is the image of
the coefficient `HJO.Sym.zmonCoeff K k w` of the *lower* level under the renaming
`MvPolynomial.rename Fin.castSucc`, times `y_{k+1}` to the number of positions of `w` carrying the
letter `k`. The three kinds of letter contribute the three factors: a letter `j < k` contributes
`y_{j+1}`, which the renaming supplies, the letter `k` contributes `y_{k+1}`, and a letter `k < j`
contributes nothing, being a letter of the alphabet. -/
theorem zmonCoeff_succ (K : Type*) [CommRing K] (k : ℕ) {N : ℕ} (w : Fin N → ℕ) :
    zmonCoeff K (k + 1) w
      = MvPolynomial.rename Fin.castSucc (zmonCoeff K k w)
        * MvPolynomial.X (Fin.last k) ^ lastAuxDegree k w := by
  classical
  have hy : (MvPolynomial.X (Fin.last k) : MvPolynomial (Fin (k + 1)) K) ^ lastAuxDegree k w
      = ∏ i : Fin N, if w i = k then MvPolynomial.X (Fin.last k) else 1 := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, lastAuxDegree]
  simp only [hy, zmonCoeff]
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rcases lt_trichotomy (w i) k with h | h | h
  · rw [zvarCoeff, dite_eq_left (show w i < k + 1 by omega), zvarCoeff, dite_eq_left h,
      MvPolynomial.rename_X, ite_eq_right (show ¬ w i = k by omega), mul_one, Fin.castSucc_mk]
  · rw [zvarCoeff, dite_eq_left (show w i < k + 1 by omega), zvarCoeff,
      dite_eq_right (show ¬ w i < k by omega), map_one, one_mul, ite_eq_left h]
    exact congrArg MvPolynomial.X (Fin.val_injective h)
  · rw [zvarCoeff, dite_eq_right (show ¬ w i < k + 1 by omega), zvarCoeff,
      dite_eq_right (show ¬ w i < k by omega), map_one, one_mul,
      ite_eq_right (show ¬ w i = k by omega)]

end HJO.Sym

namespace HJO.Dyck

open HJO.Sym

variable {K : Type*} [CommRing K] {N k : ℕ}

/-! ### The merged degree of a labelling -/

/-- **The merged degree `d(w)` of a labelling**, at the level `k + 1`: the number of positions whose
letter lies in the merged alphabet `y_{k+1}, x_1, x_2, …`, that is whose letter is at least `k`. The
labelling monomial `z^{(k+1)}_w` is a product of `N` merged variables, of which exactly these lie in
the merged alphabet, so `d(w)` is its total degree there and is at most `N`. -/
def mergedDegree (k : ℕ) {N : ℕ} (w : Fin N → ℕ) : ℕ :=
  #{i : Fin N | k ≤ w i}

/-- The merged degree is at most the number of positions, being a count of positions. This is the
degree bound `d ≤ N` of the `⨁_{d=0}^{N}`. -/
theorem mergedDegree_le (k : ℕ) {N : ℕ} (w : Fin N → ℕ) : mergedDegree k w ≤ N := by
  refine le_trans (Finset.card_filter_le _ _) ?_
  simp

/-- The alphabet degree of the labelling monomial: the number of positions whose letter lies
strictly above the level, each of which contributes a single letter of the alphabet. -/
theorem degree_zmonExponent (k : ℕ) {N : ℕ} (w : Fin N → ℕ) :
    Finsupp.degree (zmonExponent k w) = #{i : Fin N | k ≤ w i} := by
  classical
  rw [zmonExponent, map_sum, Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : w i < k
  · have h' : ¬ k ≤ w i := by omega
    simp only [zvarExponent, h, ↓reduceIte, map_zero, h', ↓reduceIte]
  · have h' : k ≤ w i := by omega
    simp only [zvarExponent, h, ↓reduceIte, Finsupp.degree_single, h', ↓reduceIte]

/-- **The merged degree splits**: at the level `k + 1` the number of positions whose letter lies in
the merged alphabet is the number carrying the distinguished letter `y_{k+1}` plus the total degree
in the alphabet of the labelling monomial. This is what supplies the witness `b` that
`HJO.Sym.zGraded` asks for, with no truncated subtraction: the exponent of `y_{k+1}` is
`HJO.Sym.lastAuxDegree k w` and the equation `lastAuxDegree k w + |zmonExponent (k+1) w| = d(w)` is
this identity. -/
theorem mergedDegree_eq_lastAuxDegree_add_degree (k : ℕ) {N : ℕ} (w : Fin N → ℕ) :
    mergedDegree k w = lastAuxDegree k w + Finsupp.degree (zmonExponent (k + 1) w) := by
  classical
  rw [mergedDegree, lastAuxDegree, degree_zmonExponent, Finset.card_filter, Finset.card_filter,
    Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> omega

/-! ### The graded parts of the characteristic series -/

/-- **The part of `χ'_σ(π)` of merged degree `d`**: the defining sum of
`HJO.Dyck.unnormalisedCharSeries` restricted to the labellings of merged degree `d`. The grouping of
the sum by `d(w)` is exactly this family, and `HJO.Dyck.sum_unnormalisedCharPart` is the statement
that it sums back to `χ'_σ(π)`.

As for `χ'_σ(π)` itself the value is given one coefficient at a time, since the sum over all the
no-attack labellings cannot be formed in `P_{k+1}`; the letters of a labelling contributing to a
given coefficient are bounded by `HJO.Dyck.zmonLetters`. -/
noncomputable def unnormalisedCharPart (q : K) (k : ℕ) {N : ℕ} (x : Fin N → ℕ)
    (σ : Fin (k + 1) → ℕ) (d : ℕ) : AuxAlphabetSeries K (k + 1) := fun e =>
  ∑ w ∈ {w ∈ {w ∈ Fintype.piFinset fun _ : Fin N => zmonLetters (k + 1) e |
      w ∈ noAttackLabellings x σ ∧ zmonExponent (k + 1) w = e} | mergedDegree k w = d},
    q ^ #(invSet (finPairs N (attackSet x)) w) • zmonCoeff K (k + 1) w

variable {q : K} {x : Fin N → ℕ} {σ : Fin (k + 1) → ℕ} {d : ℕ} {e : ℕ →₀ ℕ}

/-- The defining property of the graded part: the coefficient at the alphabet exponent `e` is the
finite sum over the no-attack labellings of merged degree `d` whose monomial has that exponent. -/
theorem coeff_unnormalisedCharPart :
    MvPowerSeries.coeff e (unnormalisedCharPart q k x σ d) =
      ∑ w ∈ {w ∈ {w ∈ Fintype.piFinset fun _ : Fin N => zmonLetters (k + 1) e |
          w ∈ noAttackLabellings x σ ∧ zmonExponent (k + 1) w = e} | mergedDegree k w = d},
        q ^ #(invSet (finPairs N (attackSet x)) w) • zmonCoeff K (k + 1) w :=
  MvPowerSeries.coeff_apply _ _

/-- Above `N` the graded parts vanish: a merged degree exceeding the number of positions is
unreachable, by `HJO.Dyck.mergedDegree_le`. This is the degree bound of the
`⨁_{d=0}^{N}`. -/
theorem unnormalisedCharPart_eq_zero (hd : N < d) : unnormalisedCharPart q k x σ d = 0 := by
  refine MvPowerSeries.ext fun e => ?_
  rw [coeff_unnormalisedCharPart, MvPowerSeries.coeff_zero]
  refine Finset.sum_eq_zero fun w hw => ?_
  obtain ⟨-, hwd⟩ := Finset.mem_filter.1 hw
  have := mergedDegree_le k w
  omega

/-- **The part of merged degree `d` lies in `Z^{(k+1)}_d`.** Its coefficient at a letter-monomial
`x^α` is a sum over labellings that all share the alphabet exponent `α` and the merged degree `d`,
hence by `HJO.Dyck.mergedDegree_eq_lastAuxDegree_add_degree` also the exponent of the distinguished
letter, which is the witness `b` with `b + |α| = d`; the coefficients of the summands are then
multiples of `y_{k+1}^b` by elements of the lower field, and a finite sum of those is one again,
which is `HJO.Sym.auxFracYPow`. Above the degree the coefficient vanishes, the same identity forcing
`|α| ≤ d` on every contributing labelling. -/
@[hjo "lem_cm_chiprime_zgraded"]
theorem auxToFrac_unnormalisedCharPart_mem_zGraded [IsDomain K] (q : K) (k : ℕ) {N : ℕ}
    (x : Fin N → ℕ) (σ : Fin (k + 1) → ℕ) (d : ℕ) :
    auxToFrac K (k + 1) (unnormalisedCharPart q k x σ d) ∈ zGraded K k d := by
  classical
  refine ⟨fun α b hb => ?_, fun α hα => ?_⟩
  · rw [← mem_auxFracYPow, coeff_auxToFrac, coeff_unnormalisedCharPart, map_sum]
    refine sum_mem fun w hw => ?_
    obtain ⟨hw', hwd⟩ := Finset.mem_filter.1 hw
    obtain ⟨-, -, hwe⟩ := Finset.mem_filter.1 hw'
    have hsplit := mergedDegree_eq_lastAuxDegree_add_degree k w
    rw [hwe] at hsplit
    have hb' : lastAuxDegree k w = b := by omega
    refine mem_auxFracYPow.2
      ⟨algebraMap (MvPolynomial (Fin k) K) (AuxFrac K k)
        (q ^ #(invSet (finPairs N (attackSet x)) w) • zmonCoeff K k w), ?_⟩
    rw [auxFracCastSucc_algebraMap, yFrac, ← map_pow, ← map_mul]
    congr 1
    rw [map_smul, smul_mul_assoc, zmonCoeff_succ, hb']
  · have h0 : MvPowerSeries.coeff α (unnormalisedCharPart q k x σ d) = 0 := by
      rw [coeff_unnormalisedCharPart]
      refine Finset.sum_eq_zero fun w hw => ?_
      obtain ⟨hw', hwd⟩ := Finset.mem_filter.1 hw
      obtain ⟨-, -, hwe⟩ := Finset.mem_filter.1 hw'
      have hsplit := mergedDegree_eq_lastAuxDegree_add_degree k w
      rw [hwe] at hsplit
      omega
    rw [coeff_auxToFrac, h0, map_zero]

/-- **The graded parts of merged degrees `0, …, N` sum to `χ'_σ(π)`.** This is the grouping of the
defining sum of `HJO.Dyck.unnormalisedCharSeries` by the merged degree `d(w)`, coefficientwise: the
labellings contributing to one coefficient are partitioned into the fibres of `d(w)`, and the fibres
are indexed by `0, …, N` because `d(w)` counts positions.

This is the identity in `P_{k+1}`, where `χ'_σ(π)` and its parts live;
`HJO.Dyck.sum_auxToFrac_unnormalisedCharPart` is the same identity in `P°_{k+1}`, where the graded
pieces `Z^{(k+1)}_d` are subsets. -/
theorem sum_unnormalisedCharPart (q : K) (k : ℕ) {N : ℕ} (x : Fin N → ℕ) (σ : Fin (k + 1) → ℕ) :
    ∑ d ∈ Finset.range (N + 1), unnormalisedCharPart q k x σ d
      = unnormalisedCharSeries q (k + 1) x σ := by
  classical
  refine MvPowerSeries.ext fun e => ?_
  rw [map_sum, coeff_unnormalisedCharSeries,
    Finset.sum_congr rfl fun d _ => coeff_unnormalisedCharPart (q := q) (x := x) (σ := σ)
      (d := d) (e := e)]
  exact Finset.sum_fiberwise_of_maps_to
    (fun w _ => Finset.mem_range.2 (Nat.lt_succ_of_le (mergedDegree_le k w))) _

/-- **The decomposition of `χ'_σ(π)` into alphabet-graded pieces**, in the ring `P°_{k+1}` where the
pieces `Z^{(k+1)}_d` of `HJO.Sym.zGraded` are subsets: the images under `HJO.Sym.auxToFrac` of the
parts of merged degrees `0, …, N` sum to the image of `χ'_σ(π)`. Together with
`HJO.Dyck.auxToFrac_unnormalisedCharPart_mem_zGraded` this is the statement
`χ'_σ(π) ∈ ⨁_{d=0}^{N}Z^{(k+1)}_d`, the sum being direct by
`HJO.Sym.eq_zero_of_sum_eq_zero_of_mem_zGraded`. -/
@[hjo "lem_cm_chiprime_zgraded"]
theorem sum_auxToFrac_unnormalisedCharPart (q : K) (k : ℕ) {N : ℕ} (x : Fin N → ℕ)
    (σ : Fin (k + 1) → ℕ) :
    ∑ d ∈ Finset.range (N + 1), auxToFrac K (k + 1) (unnormalisedCharPart q k x σ d)
      = auxToFrac K (k + 1) (unnormalisedCharSeries q (k + 1) x σ) := by
  rw [← map_sum, sum_unnormalisedCharPart]

/-- **The characteristic series is alphabet-graded**: at the level `k + 1`, the unnormalised
characteristic series `χ'_σ(π)` of a partial Dyck path with `N` positions lies in
`⨁_{d=0}^{N}Z^{(k+1)}_d`, hence in the alphabet-graded subring `Z^{(k+1)}` of `HJO.Sym.zRing`.

The family realising the decomposition is `HJO.Dyck.unnormalisedCharPart`, with
`HJO.Dyck.auxToFrac_unnormalisedCharPart_mem_zGraded` and
`HJO.Dyck.sum_unnormalisedCharPart` for its degrees and its sum, and it is the only one: the
pieces are independent by `HJO.Sym.eq_zero_of_sum_eq_zero_of_mem_zGraded`, which is what makes the
sum a direct sum. No hypothesis is imposed on the
path, on `σ` or on `N` — the `N ≥ k`, `π ∈ 𝔻_{k,N}` and pairwise distinctness of `σ` are
not used. -/
@[hjo "lem_cm_chiprime_zgraded"]
theorem auxToFrac_unnormalisedCharSeries_mem_zRing [IsDomain K] (q : K) (k : ℕ) {N : ℕ}
    (x : Fin N → ℕ) (σ : Fin (k + 1) → ℕ) :
    auxToFrac K (k + 1) (unnormalisedCharSeries q (k + 1) x σ) ∈ zRing K k := by
  refine ⟨Finset.range (N + 1), fun d => auxToFrac K (k + 1) (unnormalisedCharPart q k x σ d),
    fun d => auxToFrac_unnormalisedCharPart_mem_zGraded q k x σ d, fun d hd => ?_, ?_⟩
  · change auxToFrac K (k + 1) (unnormalisedCharPart q k x σ d) = 0
    rw [Finset.mem_range] at hd
    rw [unnormalisedCharPart_eq_zero (by omega), map_zero]
  · rw [sum_auxToFrac_unnormalisedCharPart]

end HJO.Dyck
