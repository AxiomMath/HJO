/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.LowerPartition
public import HJO.PointwiseSum
public meta import HJO.Attr

/-! # The characteristic series at the lower level

`HJO.Dyck.insertFront_partialCharSeries_identityTuple` and
`HJO.Dyck.isSummableFamily_zvar_mul_lowerCharPiece`: for a partial Dyck path `π ∈ 𝔻_{k,N}` of level
`k = m + 1`,

`Φ_m(ν_{Id_m}(π)) = ∑_{r ≥ 0} z^{(m+1)}_{m+r} μ_r(π)`,

the right-hand side being monomialwise finite. This is the lowering step of the Carlsson--Mellit
recursion read in the ring `P_{m+1}`: freeing the last special label of `Id_{k-1}` cuts the
labellings into the fibres `U(π, σ^{[r]})` of the map `w ↦ w_k - k`
(`HJO.Dyck.noAttackLabellings_lowerTuple_eq_sep`), and on the `r`-th fibre the letter at the freed
position is `m + r`, so the merged variable it contributes is constant there, comes out of the sum,
and leaves `μ_r(π)`.

## Main definitions

* `HJO.Dyck.nuLowerLetters`: the finite set of letters a labelling contributing to a fixed
  coefficient of either side can carry.

## Main results

* `HJO.Sym.insertFront_ztail`: the step
  `Φ_m(z^{(m)}_{w,♭}) = z^{(m+1)}_{w_k} z^{(m+1)}_{w,♭}`, the insertion on the free part of a
  labelling monomial.
* `HJO.Dyck.isSummableFamily_zvar_mul_lowerCharPiece`: the right-hand side is monomialwise finite.
* `HJO.Dyck.insertFront_partialCharSeries_identityTuple`: the identity above.

Three facts about a *single* merged variable feed these and are file-local: the two halves of the
comparison of `z^{(k)}_j` with `z^{(k+1)}_j`, and the bound `N` on the exponent that the free part
of a labelling of `N` positions carries at the first letter.

## Implementation notes

*The level is `m + 1` and the lower level is `m`*, as in `HJO.Dyck.lowerCharPiece` and
`HJO.Dyck.lowerTuple`, so the `k ≥ 1` is carried by the shape of the types and no truncated
subtraction `k - 1` occurs anywhere. Positions and letters are indexed from `0`, so Carlsson and
Mellit's freed label `k + r` is the letter `m + r` and their `k`-th position is the position `m`.

*The infinite sum is `HJO.Sym.summableSum`*, the monomialwise sum of `HJO.Sym.summableSum`: the
family `r ↦ z^{(m+1)}_{m+r} μ_r(π)` cannot be summed in `P_{m+1}` term by term, every member being
nonzero, but at a fixed monomial only `r = 0` and the finitely many `r = n + 1` with `n` in the
support of that monomial contribute. That is `HJO.Dyck.isSummableFamily_zvar_mul_lowerCharPiece`,
and it is part of the statement rather than a side condition — the display asserts it.

*`Φ_m` is read only through its coefficients, never as a ring homomorphism.* A direct argument
applies `Φ_{k-1}` to a monomialwise finite sum and multiplies inside it, which would need `Φ_{k-1}`
to be a ring homomorphism commuting with such sums. `HJO.Sym.insertFront` is not: it is the total
extension by `0` of the prescription at the letter-monomials where the defining sum is infinite, and
`HJO.Sym.not_injective_insertFront` records that the extension is not the intended map everywhere.
So the proof here is coefficientwise, and what replaces the homomorphism property is the two halves
of the monomial bookkeeping, `HJO.Sym.ztailExponent_eq_single_add_mapDomain` and
`HJO.Sym.ztailCoeff_succ_level_mul`, which the coefficient computation reads directly.
`HJO.Sym.insertFront_ztail` assembles them into the single step on a labelling monomial and is
recorded because it is the step the direct argument uses; a monomial is exactly where the extension
by `0` cannot fire, which is why that step survives at all.

*No boundedness side condition is needed, and that is a lemma and not an assumption.* The extension
by `0` fires where the defining sum of `HJO.Sym.insertFront` has infinite support. It does not here:
the exponent that the free part of a labelling of `N` positions carries at the first letter is at
most `N`, each free position contributing `0` or `1` there, so every coefficient of `ν_{Id_m}(π)` at
`x_1^a` with `a > N` vanishes and the sum runs over `Finset.range (N + 1)`.

*Hypotheses dropped.* The `N ≥ k` is the field `HJO.Dyck.IsPartialDyck.le_length` of the path
hypothesis and is not carried; its `k ≥ 1` is the shape of the level. The summability half needs no
hypothesis at all — it is a statement about the alphabet exponents of the merged variables and holds
for an arbitrary sequence. Two hypotheses that Carlsson and Mellit's definitions need are absent
because `HJO.Dyck.noAttackLabellings` carries none: `HJO.Dyck.IsPartialDyck.of_le_level`, putting
`π` in `𝔻_{k-1,N}` so that `U(π, Id_{k-1})` is "defined", and `HJO.Dyck.lowerTuple_injective`,
making the entries of `σ^{[r]}` distinct. Of the partition of `U(π, Id_{k-1})` into the sets
`U(π, σ^{[r]})` only the union half is read, through
`HJO.Dyck.IsPartialDyck.le_apply_of_mem_noAttackLabellings_identityTuple` and
`HJO.Dyck.noAttackLabellings_lowerTuple_eq_sep`: the sum is split along the fibres of the map
`w ↦ w_k - k`, and fibres of a map need no separate disjointness.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 4, where the identity is the first equality of the lowering computation and
their `χ'_{k,r}(π)` is `y_1 ⋯ y_{k-1} z^{(k)}_{k+r} μ_r(π)`.
-/

@[expose] public section

open Finset

namespace HJO.Sym

variable {K : Type*} [CommRing K]

/-! ### The index of the defining sum of the insertion -/

/-- The letter-monomial `x_1^a` times `e` pushed up one letter, read at the first letter: it is `a`,
the pushed-up monomial being supported away from it. -/
private theorem nuLower_index_apply_zero (a : ℕ) (e : ℕ →₀ ℕ) :
    (Finsupp.single 0 a + e.mapDomain Nat.succ : ℕ →₀ ℕ) 0 = a := by
  rw [Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.mapDomain_of_notMem_range e 0 (by simp), add_zero]

/-- The letter-monomial `x_1^a` times `e` pushed up one letter, read at the letter `n+1`: it is
`e n`, the exponent of the first letter being carried at the index `0` alone. -/
private theorem nuLower_index_apply_succ (a : ℕ) (e : ℕ →₀ ℕ) (n : ℕ) :
    (Finsupp.single 0 a + e.mapDomain Nat.succ : ℕ →₀ ℕ) (n + 1) = e n := by
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (by omega),
    Finsupp.mapDomain_apply Nat.succ_injective, zero_add]

/-- **The index of the defining sum of `Φ_k`, solved.** A letter-monomial exponent `F` is `x_1^a`
times `e` pushed up one letter exactly when its first letter carries the exponent `a` and its later
letters read off `e`. -/
private theorem nuLower_index_eq_iff {F e : ℕ →₀ ℕ} {a : ℕ} :
    F = Finsupp.single 0 a + e.mapDomain Nat.succ ↔ F 0 = a ∧ ∀ n, F (n + 1) = e n := by
  refine ⟨fun h => ?_, fun ⟨h0, h1⟩ => Finsupp.ext fun n => ?_⟩
  · subst h
    exact ⟨nuLower_index_apply_zero a e, fun n => nuLower_index_apply_succ a e n⟩
  · cases n with
    | zero => rw [h0, nuLower_index_apply_zero]
    | succ l => rw [h1, nuLower_index_apply_succ]

/-! ### The merged variables of two consecutive levels -/

/-- **The alphabet exponent of a merged variable, one level up**: discarding the first letter of
`z^{(k)}_j` leaves the exponent of `z^{(k+1)}_j`. Below the level both exponents vanish; at the
level the merged variable *is* the first letter, which is discarded, while one level up it is the
new auxiliary variable and contributes nothing; and above the level the drop of the letter index
cancels the rise of the level. -/
private theorem nuLower_zvarExponent_apply_succ (k j n : ℕ) :
    (zvarExponent k j) (n + 1) = (zvarExponent (k + 1) j) n := by
  simp only [zvarExponent]
  rcases lt_trichotomy j k with h | h | h
  · rw [ite_eq_left h, ite_eq_left (show j < k + 1 by omega)]
    rfl
  · rw [ite_eq_right (show ¬ j < k by omega), ite_eq_left (show j < k + 1 by omega),
      Finsupp.single_apply, ite_eq_right (show ¬ (j - k = n + 1) by omega)]
    rfl
  · rw [ite_eq_right (show ¬ j < k by omega), ite_eq_right (show ¬ j < k + 1 by omega),
      Finsupp.single_apply, Finsupp.single_apply]
    exact if_congr (by omega) rfl rfl

/-- **The coefficient of a merged variable, one level up**: `z^{(k+1)}_j` is `y_{k+1}` to the
exponent `z^{(k)}_j` carries at the first letter, times the coefficient of `z^{(k)}_j` renamed into
the first `k` of the new auxiliary variables. Below the level the coefficient is an auxiliary
variable and is merely renamed; at the level it is `1` below and `y_{k+1}` above, which is the first
letter being absorbed; above the level both are `1`. -/
private theorem nuLower_zvarCoeff_succ_level (K : Type*) [CommRing K] (k j : ℕ) :
    zvarCoeff K (k + 1) j =
      MvPolynomial.X (Fin.last k) ^ (zvarExponent k j) 0 *
        MvPolynomial.rename Fin.castSucc (zvarCoeff K k j) := by
  simp only [zvarCoeff, zvarExponent]
  rcases lt_trichotomy j k with h | h | h
  · rw [dite_eq_left (show j < k + 1 by omega), dite_eq_left h, ite_eq_left h,
      MvPolynomial.rename_X, Fin.castSucc_mk]
    simp
  · subst h
    rw [dite_eq_left (Nat.lt_succ_self j), dite_eq_right (lt_irrefl j),
      ite_eq_right (lt_irrefl j), Nat.sub_self, Finsupp.single_eq_same, map_one, mul_one, pow_one]
    rfl
  · rw [dite_eq_right (show ¬ j < k + 1 by omega), dite_eq_right (show ¬ j < k by omega),
      ite_eq_right (show ¬ j < k by omega), Finsupp.single_apply,
      ite_eq_right (show ¬ (j - k = 0) by omega), map_one, pow_zero, mul_one]

/-! ### The free positions of two consecutive levels -/

/-- The positions at or above the level `m` are the position `m` itself together with the positions
at or above `m + 1`: the one position the lowering step frees, and the free positions of the level
above. -/
private theorem nuLower_filter_le_eq_insert {N m : ℕ} {p : Fin N} (hp : (p : ℕ) = m) :
    ({i : Fin N | m ≤ (i : ℕ)} : Finset (Fin N))
      = insert p ({i : Fin N | m + 1 ≤ (i : ℕ)} : Finset (Fin N)) := by
  refine Finset.ext fun i => ?_
  simp only [Finset.mem_insert, mem_filter_univ]
  refine ⟨fun hi => ?_, ?_⟩
  · rcases Nat.lt_or_ge (i : ℕ) (m + 1) with hlt | hge
    · exact Or.inl (Fin.ext (by omega))
    · exact Or.inr hge
  · rintro (rfl | hi) <;> omega

/-- The freed position is not one of the free positions of the level above. -/
private theorem nuLower_notMem_filter_le {N m : ℕ} {p : Fin N} (hp : (p : ℕ) = m) :
    p ∉ ({i : Fin N | m + 1 ≤ (i : ℕ)} : Finset (Fin N)) := fun hcon => by
  have := mem_filter_univ p |>.1 hcon
  omega

/-- **A labelling of `N` positions contributes at most `N` to the exponent of the first letter** of
its free part: each free position contributes `0` or `1` there. This is why no boundedness
hypothesis is needed in `HJO.Dyck.insertFront_partialCharSeries_identityTuple` — the sum defining
`Φ_m` on `ν_σ(π)` is supported in `Finset.range (N + 1)`, so the extension by `0` of
`HJO.Sym.insertFront` never fires. -/
private theorem nuLower_ztailExponent_apply_zero_le (k : ℕ) {N : ℕ} (w : Fin N → ℕ) :
    (ztailExponent k w) 0 ≤ N := by
  rw [ztailExponent, Finsupp.finsetSum_apply]
  calc ∑ i ∈ ({i : Fin N | k ≤ (i : ℕ)} : Finset (Fin N)), (zvarExponent k (w i)) 0
      ≤ ∑ _i ∈ ({i : Fin N | k ≤ (i : ℕ)} : Finset (Fin N)), 1 :=
        Finset.sum_le_sum fun i _ => by
          simp only [zvarExponent]
          by_cases h : w i < k
          · rw [ite_eq_left h]
            simp
          · rw [ite_eq_right h, Finsupp.single_apply]
            split <;> omega
    _ ≤ N := by simpa using Finset.card_filter_le (Finset.univ : Finset (Fin N)) _

/-! ### The insertion on the free part of a labelling monomial -/

/-- **The alphabet exponent of the free part of a labelling monomial, one level up.** The exponent
of `z^{(m)}_{w,♭}` is `x_1` to the exponent it carries there times the exponent of
`z^{(m+1)}_{w_k} z^{(m+1)}_{w,♭}` pushed up one letter. This is the exponent half of the
step `Φ_m(z^{(m)}_{w,♭}) = z^{(m+1)}_{w_k} z^{(m+1)}_{w,♭}`: the freed position leaves the free part
and contributes its own merged variable, and each letter's exponent moves one place down. -/
theorem ztailExponent_eq_single_add_mapDomain (m : ℕ) {N : ℕ} (w : Fin N → ℕ) {p : Fin N}
    (hp : (p : ℕ) = m) :
    ztailExponent m w = Finsupp.single 0 ((ztailExponent m w) 0) +
      (zvarExponent (m + 1) (w p) + ztailExponent (m + 1) w).mapDomain Nat.succ := by
  refine nuLower_index_eq_iff.2 ⟨rfl, fun n => ?_⟩
  have h1 : (ztailExponent m w) (n + 1)
      = ∑ i ∈ ({i : Fin N | m ≤ (i : ℕ)} : Finset (Fin N)), (zvarExponent (m + 1) (w i)) n := by
    rw [ztailExponent, Finsupp.finsetSum_apply]
    exact Finset.sum_congr rfl fun i _ => nuLower_zvarExponent_apply_succ m (w i) n
  have h2 : (ztailExponent (m + 1) w) n
      = ∑ i ∈ ({i : Fin N | m + 1 ≤ (i : ℕ)} : Finset (Fin N)),
        (zvarExponent (m + 1) (w i)) n := by
    rw [ztailExponent, Finsupp.finsetSum_apply]
  rw [Finsupp.add_apply, h1, h2, nuLower_filter_le_eq_insert hp,
    Finset.sum_insert (nuLower_notMem_filter_le hp)]

/-- **The coefficient of the free part of a labelling monomial, one level up.** The coefficient of
`z^{(m+1)}_{w_k} z^{(m+1)}_{w,♭}` is `y_{m+1}` to the exponent `z^{(m)}_{w,♭}` carries at the first
letter, times the coefficient of `z^{(m)}_{w,♭}` renamed into the old auxiliary variables. This is
the coefficient half of the step, the letters equal to `m` at the free positions having
become the new auxiliary variable. -/
theorem ztailCoeff_succ_level_mul (K : Type*) [CommRing K] (m : ℕ) {N : ℕ} (w : Fin N → ℕ)
    {p : Fin N} (hp : (p : ℕ) = m) :
    zvarCoeff K (m + 1) (w p) * ztailCoeff K (m + 1) w =
      MvPolynomial.X (Fin.last m) ^ (ztailExponent m w) 0 *
        MvPolynomial.rename Fin.castSucc (ztailCoeff K m w) := by
  have hprod : ∏ i ∈ ({i : Fin N | m ≤ (i : ℕ)} : Finset (Fin N)), zvarCoeff K (m + 1) (w i)
      = MvPolynomial.X (Fin.last m) ^ (ztailExponent m w) 0 *
        MvPolynomial.rename Fin.castSucc (ztailCoeff K m w) := by
    rw [Finset.prod_congr rfl (fun i _ => nuLower_zvarCoeff_succ_level K m (w i)),
      Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ztailCoeff, ← map_prod, ztailExponent,
      Finsupp.finsetSum_apply]
  rw [← hprod, nuLower_filter_le_eq_insert hp, Finset.prod_insert (nuLower_notMem_filter_le hp),
    ztailCoeff]

/-- The insertion on a monomial of `P_k`: substituting `y_{k+1}` for the first letter turns the
monomial `x_1^a` times `x^d` pushed up one letter, with coefficient `c`, into `x^d` with coefficient
`y_{k+1}^a c`, the old auxiliary variables being renamed. The defining sum of
`HJO.Sym.insertFront` has a single nonzero term here, so its extension by `0` cannot fire. -/
private theorem nuLower_insertFront_monomial (k a : ℕ) (d : ℕ →₀ ℕ)
    (c : MvPolynomial (Fin k) K) :
    insertFront K k (MvPowerSeries.monomial (Finsupp.single 0 a + d.mapDomain Nat.succ) c) =
      MvPowerSeries.monomial d (MvPolynomial.X (Fin.last k) ^ a *
        MvPolynomial.rename Fin.castSucc c) := by
  refine MvPowerSeries.ext fun e => ?_
  have hrhs : MvPowerSeries.coeff e (MvPowerSeries.monomial d
        (MvPolynomial.X (Fin.last k) ^ a * MvPolynomial.rename Fin.castSucc c))
      = if e = d then MvPolynomial.X (Fin.last k) ^ a *
          MvPolynomial.rename Fin.castSucc c else 0 := by
    rw [MvPowerSeries.coeff_monomial]
  rw [coeff_insertFront, hrhs]
  by_cases he : e = d
  · rw [ite_eq_left he, he]
    have hsingle : ∀ b : ℕ, b ≠ a → MvPolynomial.X (Fin.last k) ^ b *
        MvPolynomial.rename Fin.castSucc
          (MvPowerSeries.coeff (Finsupp.single 0 b + d.mapDomain Nat.succ)
            (MvPowerSeries.monomial (Finsupp.single 0 a + d.mapDomain Nat.succ) c)) = 0 := by
      intro b hb
      rw [MvPowerSeries.coeff_monomial, ite_eq_right, map_zero, mul_zero]
      intro hcon
      refine hb ?_
      have h0 := congrArg (fun f : ℕ →₀ ℕ => f 0) hcon
      rwa [nuLower_index_apply_zero, nuLower_index_apply_zero] at h0
    rw [finsum_eq_single _ a hsingle, MvPowerSeries.coeff_monomial_same]
  · rw [ite_eq_right he]
    refine finsum_eq_zero_of_forall_eq_zero fun b => ?_
    rw [MvPowerSeries.coeff_monomial, ite_eq_right, map_zero, mul_zero]
    intro hcon
    refine he (Finsupp.ext fun n => ?_)
    have hn := congrArg (fun f : ℕ →₀ ℕ => f (n + 1)) hcon
    rwa [nuLower_index_apply_succ, nuLower_index_apply_succ] at hn

/-- **The insertion on the free part of a labelling monomial**, the step

`Φ_m(z^{(m)}_{w,♭}) = z^{(m+1)}_{w_k} · z^{(m+1)}_{w,♭}`,

for a position `p` of index `m`. The free part is a monomial of `P_m`
(`HJO.Sym.ztail_eq_monomial`), `Φ_m` is the substitution `x_1 ↦ y_{m+1}` on a monomial, and the two
halves of the bookkeeping are `HJO.Sym.ztailExponent_eq_single_add_mapDomain` and
`HJO.Sym.ztailCoeff_succ_level_mul`: the freed position leaves the free part of the level above and
contributes the single merged variable `z^{(m+1)}_{w_p}` instead.

This is the reading of `HJO.Sym.insertFront_zvar` on a product of merged variables, and it
holds although `HJO.Sym.insertFront` is not a ring homomorphism — a monomial is where its extension
by `0` cannot fire. -/
theorem insertFront_ztail (K : Type*) [CommRing K] (m : ℕ) {N : ℕ} (w : Fin N → ℕ) {p : Fin N}
    (hp : (p : ℕ) = m) :
    insertFront K m (ztail K m w) = zvar K (m + 1) (w p) * ztail K (m + 1) w := by
  rw [ztail_eq_monomial, ztailExponent_eq_single_add_mapDomain m w hp,
    nuLower_insertFront_monomial, zvar_eq_monomial, ztail_eq_monomial,
    MvPowerSeries.monomial_mul_monomial, ztailCoeff_succ_level_mul K m w hp]

end HJO.Sym

namespace HJO.Dyck

open HJO.Sym

variable {K : Type*} [CommRing K]

/-! ### The letters of a contributing labelling -/

/-- **The letters available to a labelling contributing to the coefficient of `x^e`** on either side
of `HJO.Dyck.insertFront_partialCharSeries_identityTuple`: the letters below `m + 1`, which name
auxiliary variables of the level `m + 1` and so leave no trace in `e`, and the letters `n + 1 + m`
for `n` in the support of `e`, which name the letters of the alphabet that `e` records, read at the
lower level where they are shifted by one more place.

This single finite set bounds the labellings summed on the left — the labellings of `ν_{Id_m}(π)`
reaching the letter-monomials `x_1^a` times `e` pushed up one letter, which are the ones `Φ_m` reads
— and those summed on the right, in each piece `μ_r(π)` with `r` among the finitely many indices
that reach `e`. -/
def nuLowerLetters (m : ℕ) (e : ℕ →₀ ℕ) : Finset ℕ :=
  Finset.range (m + 1) ∪ e.support.image (fun n => n + 1 + m)

theorem mem_nuLowerLetters_of_lt {m : ℕ} {e : ℕ →₀ ℕ} {j : ℕ} (hj : j < m + 1) :
    j ∈ nuLowerLetters m e :=
  Finset.mem_union_left _ (Finset.mem_range.2 hj)

theorem mem_nuLowerLetters_of_apply_ne_zero {m : ℕ} {e : ℕ →₀ ℕ} {n : ℕ} (hn : e n ≠ 0) :
    n + 1 + m ∈ nuLowerLetters m e :=
  Finset.mem_union_right _ (Finset.mem_image.2 ⟨n, Finsupp.mem_support_iff.2 hn, rfl⟩)

/-- The letters of a labelling of `π` prescribed by `Id_m` that contributes to the coefficient of
`ν_{Id_m}(π)` at `x_1^a` times `e` pushed up one letter. -/
private theorem nuLower_nuLetters_subset_lower (m : ℕ) (e : ℕ →₀ ℕ) (a : ℕ) :
    nuLetters m (Finsupp.single 0 a + e.mapDomain Nat.succ) (identityTuple m)
      ⊆ nuLowerLetters m e := by
  intro j hj
  rw [nuLetters, Finset.mem_union, Finset.mem_union] at hj
  rcases hj with (hj | hj) | hj
  · exact mem_nuLowerLetters_of_lt (by have := Finset.mem_range.1 hj; omega)
  · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hj
    cases n with
    | zero => exact mem_nuLowerLetters_of_lt (by omega)
    | succ l =>
      have hl := Finsupp.mem_support_iff.1 hn
      rw [nuLower_index_apply_succ] at hl
      exact mem_nuLowerLetters_of_apply_ne_zero hl
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hj
    exact mem_nuLowerLetters_of_lt (Nat.lt_succ_of_lt (identityTuple_lt m i))

/-- The letters of a labelling of `π` prescribed by `σ^{[r]}` that contributes to the coefficient of
`μ_r(π)` at a letter-monomial below `e`, for one of the finitely many `r` that reach `e`. -/
private theorem nuLower_nuLetters_subset_piece {m : ℕ} {e : ℕ →₀ ℕ} {r : ℕ}
    (hr : r ∈ insert 0 (e.support.image (· + 1))) {t : ℕ →₀ ℕ} (ht : t ≤ e) :
    nuLetters (m + 1) t (lowerTuple m r) ⊆ nuLowerLetters m e := by
  have hmr : m + r ∈ nuLowerLetters m e := by
    rcases Finset.mem_insert.1 hr with rfl | hr'
    · exact mem_nuLowerLetters_of_lt (by omega)
    · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hr'
      rw [show m + (n + 1) = n + 1 + m by omega]
      exact mem_nuLowerLetters_of_apply_ne_zero (Finsupp.mem_support_iff.1 hn)
  intro j hj
  rw [nuLetters, Finset.mem_union, Finset.mem_union] at hj
  rcases hj with (hj | hj) | hj
  · exact mem_nuLowerLetters_of_lt (Finset.mem_range.1 hj)
  · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hj
    rw [show n + (m + 1) = n + 1 + m by omega]
    refine mem_nuLowerLetters_of_apply_ne_zero ?_
    have h1 := Finsupp.mem_support_iff.1 hn
    have h2 : t n ≤ e n := Finsupp.le_def.1 ht n
    omega
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hj
    induction i using Fin.lastCases with
    | last =>
      rw [lowerTuple_last]
      exact hmr
    | cast l =>
      rw [lowerTuple_castSucc]
      exact mem_nuLowerLetters_of_lt (by have := l.isLt; omega)

/-! ### The right-hand side is monomialwise finite -/

/-- The exponent of the freed merged variable at `r = 0`: the letter `m` lies below the level
`m + 1`, so `z^{(m+1)}_m` is the auxiliary variable `y_{m+1}` and leaves no trace in the
alphabet. -/
private theorem nuLower_zvarExponent_zero (m : ℕ) : zvarExponent (m + 1) (m + 0) = 0 := by
  rw [zvarExponent, ite_eq_left (by omega)]

/-- The exponent of the freed merged variable at `r = n + 1`: the letter `m + r` lies above the
level `m + 1`, so `z^{(m+1)}_{m+r}` is the letter `x_r` of the alphabet. -/
private theorem nuLower_zvarExponent_succ (m n : ℕ) :
    zvarExponent (m + 1) (m + (n + 1)) = Finsupp.single n 1 := by
  rw [zvarExponent, ite_eq_right (show ¬ m + (n + 1) < m + 1 by omega),
    show m + (n + 1) - (m + 1) = n by omega]

/-- A piece outside the finitely many that reach a monomial contributes nothing there: for `r ≥ 1`
the merged variable `z^{(m+1)}_{m+r}` is the letter `x_r`, so the product it multiplies has no
coefficient at a monomial from which that letter is absent. -/
private theorem nuLower_coeff_eq_zero (q : K) (m : ℕ) {N : ℕ} (x : Fin N → ℕ) (e : ℕ →₀ ℕ) {r : ℕ}
    (hr : r ∉ insert 0 (e.support.image (· + 1))) :
    MvPowerSeries.coeff e (zvar K (m + 1) (m + r) * lowerCharPiece q m x r) = 0 := by
  have hr0 : r ≠ 0 := fun hcon => hr (by rw [hcon]; exact Finset.mem_insert_self 0 _)
  obtain ⟨l, rfl⟩ : ∃ l, r = l + 1 := ⟨r - 1, by omega⟩
  have hel : e l = 0 := by
    by_contra hcon
    exact hr (Finset.mem_insert_of_mem
      (Finset.mem_image.2 ⟨l, Finsupp.mem_support_iff.2 hcon, rfl⟩))
  rw [zvar_eq_monomial, nuLower_zvarExponent_succ, MvPowerSeries.coeff_monomial_mul,
    ite_eq_right fun hle => absurd (Finsupp.single_le_iff.1 hle) (by omega)]

/-- **The right-hand side of `HJO.Dyck.insertFront_partialCharSeries_identityTuple` is monomialwise
finite**: the family `r ↦ z^{(m+1)}_{m+r} μ_r(π)` is summable in the sense of
`HJO.Sym.IsSummableFamily`. At a monomial `x^e` only `r = 0` and the `r = n + 1` with `n` in the
support of `e` contribute, the merged variable `z^{(m+1)}_{m+r}` being the letter `x_r` for `r ≥ 1`.

This is the second clause of the display, and it needs no hypothesis: it is a statement
about the alphabet exponents of the merged variables and holds for an arbitrary sequence `x`. -/
@[hjo "lem_cm_nu_lower"]
theorem isSummableFamily_zvar_mul_lowerCharPiece (q : K) (m : ℕ) {N : ℕ} (x : Fin N → ℕ) :
    IsSummableFamily fun r : ℕ => zvar K (m + 1) (m + r) * lowerCharPiece q m x r := by
  refine isSummableFamily_iff.2 fun e => Set.Finite.subset
    (insert 0 (e.support.image (· + 1)) : Finset ℕ).finite_toSet fun r hr => ?_
  simp only [Function.mem_support, ne_eq] at hr
  rw [Finset.mem_coe]
  by_contra hcon
  exact hr (nuLower_coeff_eq_zero q m x e hcon)

/-! ### The characteristic series at the lower level -/

/-- **`HJO.Dyck.insertFront_partialCharSeries_identityTuple`: the characteristic series at the lower
level**,

`Φ_m(ν_{Id_m}(π)) = ∑_{r ≥ 0} z^{(m+1)}_{m+r} μ_r(π)`,

for a partial Dyck path `π ∈ 𝔻_{k,N}` of level `k = m + 1`. The right-hand side is monomialwise
finite by `HJO.Dyck.isSummableFamily_zvar_mul_lowerCharPiece` and is formed as
`HJO.Sym.summableSum`.

The proof is Carlsson and Mellit's, read coefficientwise. Fix a monomial `x^e` of `P_{m+1}`. On the
left, the coefficient of `Φ_m(ν_{Id_m}(π))` there is the sum over the exponent `a` of the first
letter of `y_{m+1}^a` against the coefficient of `ν_{Id_m}(π)` at `x_1^a` times `e` pushed up one
letter; that sum is finite because the exponent of the first letter is bounded by `N`, and
regrouping the labellings by `a` turns it into a single sum over the `w ∈ U(π, Id_m)` whose free
part is carried to `x^e`. The two halves of that carrying are
`HJO.Sym.ztailExponent_eq_single_add_mapDomain` and `HJO.Sym.ztailCoeff_succ_level_mul`, which
together are the `Φ_m(z^{(m)}_{w,♭}) = z^{(m+1)}_{w_k} z^{(m+1)}_{w,♭}`
(`HJO.Sym.insertFront_ztail`). Splitting that sum along the fibres of `w ↦ w_k - k` then gives the
pieces: on the `r`-th fibre the letter at the freed position is `m + r`, so the factor
`z^{(m+1)}_{m+r}` is constant there and comes out, leaving `μ_r(π)`.

Only the union half of the partition into the sets `U(π, σ^{[r]})` is read — the
fibres of a map are disjoint — and the hypothesis `N ≥ k` is the field
`HJO.Dyck.IsPartialDyck.le_length` of the path hypothesis, so it is not carried. No boundedness side
condition is needed although `HJO.Sym.insertFront` is only the total extension by `0` of the
`Φ_m`. -/
@[hjo "lem_cm_nu_lower"]
theorem insertFront_partialCharSeries_identityTuple (q : K) {m N : ℕ} {x : Fin N → ℕ}
    (h : IsPartialDyck (m + 1) N x) :
    insertFront K m (partialCharSeries q m x (identityTuple m)) =
      summableSum fun r : ℕ => zvar K (m + 1) (m + r) * lowerCharPiece q m x r := by
  have hm : m < N := h.le_length
  obtain ⟨p, hp⟩ : ∃ p : Fin N, (p : ℕ) = m := ⟨⟨m, hm⟩, rfl⟩
  refine MvPowerSeries.ext fun e => ?_
  -- The index set on the left: the labellings whose free part is carried to the monomial `x^e`.
  set W : Finset (Fin N → ℕ) := {w ∈ Fintype.piFinset fun _ : Fin N => nuLowerLetters m e |
      w ∈ noAttackLabellings x (identityTuple m) ∧
        zvarExponent (m + 1) (w p) + ztailExponent (m + 1) w = e} with hWdef
  have hWmem : ∀ w : Fin N → ℕ, w ∈ W ↔ ((∀ i, w i ∈ nuLowerLetters m e) ∧
      w ∈ noAttackLabellings x (identityTuple m) ∧
        zvarExponent (m + 1) (w p) + ztailExponent (m + 1) w = e) := fun w => by
    rw [hWdef, Finset.mem_filter, Fintype.mem_piFinset]
  -- The letter at the freed position is at least `m`, every earlier position attacking it: the
  -- content of the union half of `HJO.Dyck.pairwise_disjoint_noAttackLabellings_lowerTuple`.
  have hle : ∀ w ∈ W, m ≤ w p := fun w hw =>
    h.le_apply_of_mem_noAttackLabellings_identityTuple ((hWmem w).1 hw).2.1 hp
  -- Each labelling of `W` lies in one of the finitely many pieces that reach `x^e`.
  have hmaps : ∀ w ∈ W, w p - m ∈ insert 0 (e.support.image (· + 1)) := by
    intro w hw
    obtain ⟨-, -, hDw⟩ := (hWmem w).1 hw
    have hwm := hle w hw
    rcases Nat.eq_zero_or_pos (w p - m) with h0 | h0
    · rw [h0]
      exact Finset.mem_insert_self _ _
    · obtain ⟨n, hn⟩ : ∃ n, w p = m + (n + 1) := ⟨w p - m - 1, by omega⟩
      have hsle : Finsupp.single n 1 ≤ e := by
        rw [← hDw, hn, nuLower_zvarExponent_succ]
        exact le_self_add
      have hen : e n ≠ 0 := by
        have := Finsupp.single_le_iff.1 hsle
        omega
      rw [show w p - m = n + 1 by omega]
      exact Finset.mem_insert_of_mem
        (Finset.mem_image.2 ⟨n, Finsupp.mem_support_iff.2 hen, rfl⟩)
  -- Every coefficient of `ν_{Id_m}(π)` at a high power of the first letter vanishes.
  have hvan : ∀ a : ℕ, N < a → MvPowerSeries.coeff (Finsupp.single 0 a + e.mapDomain Nat.succ)
      (partialCharSeries q m x (identityTuple m)) = 0 := by
    intro a ha
    rw [coeff_partialCharSeries]
    refine Finset.sum_eq_zero fun w hw => ?_
    exfalso
    have h1 := nuLower_ztailExponent_apply_zero_le m w
    rw [(Finset.mem_filter.1 hw).2.2, nuLower_index_apply_zero] at h1
    omega
  -- The index of the defining sum of `Φ_m`, solved at the free part of a labelling.
  have hindex : ∀ (w : Fin N → ℕ) (a : ℕ),
      ztailExponent m w = Finsupp.single 0 a + e.mapDomain Nat.succ ↔
        (ztailExponent m w) 0 = a ∧
          zvarExponent (m + 1) (w p) + ztailExponent (m + 1) w = e := by
    intro w a
    have hkey : ∀ n, (ztailExponent m w) (n + 1)
        = (zvarExponent (m + 1) (w p) + ztailExponent (m + 1) w) n := fun n => by
      conv_lhs => rw [ztailExponent_eq_single_add_mapDomain m w hp]
      rw [nuLower_index_apply_succ]
    rw [nuLower_index_eq_iff]
    exact ⟨fun hc => ⟨hc.1, Finsupp.ext fun n => (hkey n).symm.trans (hc.2 n)⟩,
      fun hc => ⟨hc.1, fun n => (hkey n).trans (by rw [hc.2])⟩⟩
  -- The left-hand side, coefficientwise: a single sum over the labellings of `W`.
  have hL : MvPowerSeries.coeff e (insertFront K m (partialCharSeries q m x (identityTuple m)))
      = ∑ w ∈ W, zvarCoeff K (m + 1) (w p) *
          (q ^ #(invSet (finPairs N (attackSet x)) w) • ztailCoeff K (m + 1) w) := by
    have hsupp : (Function.support fun a : ℕ => MvPolynomial.X (Fin.last m) ^ a *
        MvPolynomial.rename Fin.castSucc
          (MvPowerSeries.coeff (Finsupp.single 0 a + e.mapDomain Nat.succ)
            (partialCharSeries q m x (identityTuple m)))) ⊆ ↑(Finset.range (N + 1)) := by
      intro a ha
      simp only [Function.mem_support, ne_eq] at ha
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hcon
      exact ha (by rw [hvan a (by omega), map_zero, mul_zero])
    rw [coeff_insertFront, finsum_eq_sum_of_support_subset _ hsupp,
      ← Finset.sum_fiberwise_of_maps_to (g := fun w : Fin N → ℕ => (ztailExponent m w) 0)
        (t := Finset.range (N + 1)) fun w _ => Finset.mem_range.2
          (Nat.lt_succ_of_le (nuLower_ztailExponent_apply_zero_le m w))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coeff_partialCharSeries_of_subset (nuLower_nuLetters_subset_lower m e a), map_sum,
      Finset.mul_sum]
    refine Finset.sum_congr (Finset.ext fun w => ?_) fun w hw => ?_
    · rw [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_filter, hWmem w]
      refine ⟨fun hc => ?_, fun hc => ⟨hc.1.1, hc.1.2.1, (hindex w a).2 ⟨hc.2, hc.1.2.2⟩⟩⟩
      obtain ⟨h1, h2⟩ := (hindex w a).1 hc.2.2
      exact ⟨⟨hc.1, hc.2.1, h2⟩, h1⟩
    · have ha : (ztailExponent m w) 0 = a := (Finset.mem_filter.1 hw).2
      rw [map_smul, mul_smul_comm, ← ha, ← ztailCoeff_succ_level_mul K m w hp, ← mul_smul_comm]
  -- The `r`-th summand on the right, coefficientwise: the labellings of the `r`-th fibre.
  have hR : ∀ r ∈ insert 0 (e.support.image (· + 1)),
      MvPowerSeries.coeff e (zvar K (m + 1) (m + r) * lowerCharPiece q m x r)
        = ∑ w ∈ {w ∈ W | w p - m = r}, zvarCoeff K (m + 1) (w p) *
            (q ^ #(invSet (finPairs N (attackSet x)) w) • ztailCoeff K (m + 1) w) := by
    intro r hr
    have hd : zvarExponent (m + 1) (m + r) ≤ e := by
      rcases Finset.mem_insert.1 hr with rfl | hr'
      · rw [nuLower_zvarExponent_zero]
        exact Finsupp.le_def.2 fun n => by simp
      · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hr'
        rw [nuLower_zvarExponent_succ]
        exact Finsupp.single_le_iff.2 (by have := Finsupp.mem_support_iff.1 hn; omega)
    have hte : zvarExponent (m + 1) (m + r) + (e - zvarExponent (m + 1) (m + r)) = e :=
      add_tsub_cancel_of_le hd
    have hts : (e - zvarExponent (m + 1) (m + r)) ≤ e := Finsupp.le_def.2 fun n => by
      rw [Finsupp.tsub_apply]
      omega
    rw [zvar_eq_monomial, lowerCharPiece_eq_partialCharSeries, MvPowerSeries.coeff_monomial_mul,
      ite_eq_left hd, coeff_partialCharSeries_of_subset (nuLower_nuLetters_subset_piece hr hts),
      Finset.mul_sum]
    refine Finset.sum_congr (Finset.ext fun w => ?_) fun w hw => ?_
    · rw [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_filter, hWmem w,
        noAttackLabellings_lowerTuple_eq_sep x r hp]
      refine ⟨fun hc => ?_, fun hc => ?_⟩
      · obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := hc
        refine ⟨⟨h1, h2, ?_⟩, by omega⟩
        rw [h3, h4]
        exact hte
      · obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hc
        have hwp : w p = m + r := by
          have := hle w ((hWmem w).2 ⟨h1, h2, h3⟩)
          omega
        refine ⟨h1, ⟨h2, hwp⟩, ?_⟩
        rw [hwp] at h3
        rw [← h3, add_tsub_cancel_left]
    · have hwp : w p = m + r := by
        have h1 := (Finset.mem_filter.1 hw).1
        have h2 := hle w h1
        have h3 := (Finset.mem_filter.1 hw).2
        omega
      rw [hwp]
  -- The two sides, matched along the fibres.
  have hRsum : MvPowerSeries.coeff e
        (summableSum fun r : ℕ => zvar K (m + 1) (m + r) * lowerCharPiece q m x r)
      = ∑ r ∈ insert 0 (e.support.image (· + 1)),
        MvPowerSeries.coeff e (zvar K (m + 1) (m + r) * lowerCharPiece q m x r) :=
    coeff_summableSum_eq_sum fun r hr => by
      by_contra hcon
      exact hr (nuLower_coeff_eq_zero q m x e hcon)
  rw [hL, hRsum, Finset.sum_congr rfl hR]
  exact (Finset.sum_fiberwise_of_maps_to hmaps _).symm

end HJO.Dyck
