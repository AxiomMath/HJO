/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.EastLabelling
public import HJO.CarlssonMellit.EastStep
public import HJO.CarlssonMellit.InsertZvar
public import HJO.CarlssonMellit.PartialCharSeries
public meta import HJO.Attr

/-! # The characteristic series after prepending an east step

One lemma, `HJO.Dyck.partialCharSeries_prependEast`: for `k ≤ N` and a partial Dyck path
`π` of length `N`,

`ν_{σ^{(k+1)}}(E_kπ) = q^k Φ_k(ν_{Id_k}(π))`.

The raising step of the Carlsson--Mellit recursion prepends an east step to `π`, prepends the new
special letter to each labelling, and replaces the level `k` by `k + 1`. All three moves are already
available: `HJO.Dyck.bijOn_prependLabel_noAttackLabellings` indexes the labellings of `E_kπ`
prescribed by `σ^{(k+1)}` by the labellings of `π` prescribed by `Id_k`, and
`HJO.Dyck.invNumber_prependEast_prependLabel` says the reindexing costs exactly `k` inversions. What
this file adds is the effect of the move on the *monomial* a labelling contributes, and that is the
whole content of the insertion `Φ_k` here.

## Main definitions

* `HJO.Sym.dropLetter`: a letter-monomial exponent with its first letter discarded and every later
  letter moved down one place, the exponent bookkeeping of `Φ_k`.

## Main results

* `HJO.Dyck.ztailExponent_prependLabel` and `HJO.Dyck.ztailCoeff_prependLabel`: the free part
  `z^{(k+1)}_{E^*_kw,♭}` of the prepended labelling is the image under `Φ_k` of the free part
  `z^{(k)}_{w,♭}`, read on the two halves of the monomial: the alphabet exponent drops a letter, and
  the coefficient in the auxiliary variables picks up `y_{k+1}` to the exponent of the first letter.
* `HJO.Dyck.partialCharSeries_prependEast`: the identity above.

## Implementation notes

*`Φ_k` is applied only through its coefficients, never as a ring homomorphism.* A direct
proof multiplies inside `Φ_k` and sums inside `Φ_k`, which needs `Φ_k` to be a `𝕜`-algebra map
commuting with monomialwise finite sums; `HJO.Sym.insertFront` is a bare function, the *total
extension by* `0` of the prescription, and the docstring of `HJO.Sym.insertFront`
records that the prescription is not everywhere defined. So the proof here is coefficientwise
throughout: the coefficient of `Φ_k(ν_{Id_k}(π))` at a letter-monomial `e` is the sum, over the
number `a` of first letters absorbed, of `y_{k+1}^a` against the coefficient of `ν_{Id_k}(π)` at
`x_1^a` times `e` moved up one letter, and the labellings of `π` are grouped by that `a`.

*No boundedness side condition is needed, and that is a lemma and not an assumption.* The extension
by `0` fires exactly where the defining `finsum` has infinite support, so the statement is the
intended one only if every one of those sums is finite at `ν_{Id_k}(π)`. It is:
`HJO.Dyck.ztailExponent_apply_zero_le` says a labelling of `N` positions contributes at most `N` to
the exponent of the first letter, so every coefficient of `ν_{Id_k}(π)` at `x_1^a` with `a > N`
vanishes and the `finsum` is a sum over `Finset.range (N + 1)`. The defect in `HJO.Sym.insertFront`
is therefore invisible here, at the cost of that bound being proved rather than assumed.

*The hypothesis is `k ≤ N` and not `π ∈ 𝔻_{k,N}`*, the two inputs from the east-step files asking
for no more: the bijection of labellings asks for nothing at all and the inversion count asks for
`k ≤ N` and the prescription, which the labellings carry. Nothing in the argument reads the path
condition, so it is dropped rather than carried.

*Positions, letters and levels are indexed from `0`*, as everywhere in this layer, so the
`σ^{(k+1)}` of the display above is `HJO.Dyck.cycleTuple (Fin.last k)`, `E^*_k` is
`HJO.Dyck.prependLabel k`, and `z^{(k)}_{w,♭}` is `HJO.Sym.ztail K k w`.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 4. Consumed by `HJO.Dyck.isSigmaCharacter_cmDPlus`. -/

@[expose] public section

open Finset HJO.Sym

namespace HJO.Sym

/-! ### Discarding the first letter of a monomial -/

/-- **A letter-monomial exponent with its first letter discarded**, every later letter moving down
one place: the value at `n` is the value of `e` at `n + 1`. This is the bookkeeping the insertion
`Φ_k` does on the alphabet, the first letter `x₁` being absorbed into the new auxiliary variable
`y_{k+1}` and every later letter dropping one place. -/
noncomputable def dropLetter (e : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  e.comapDomain Nat.succ Nat.succ_injective.injOn

@[simp]
theorem dropLetter_apply (e : ℕ →₀ ℕ) (n : ℕ) : dropLetter e n = e (n + 1) :=
  Finsupp.comapDomain_apply _ _ _ _

theorem dropLetter_sum {ι : Type*} (s : Finset ι) (f : ι → (ℕ →₀ ℕ)) :
    dropLetter (∑ i ∈ s, f i) = ∑ i ∈ s, dropLetter (f i) :=
  Finsupp.ext fun n => by
    rw [dropLetter_apply, Finsupp.finsetSum_apply, Finsupp.finsetSum_apply]
    exact Finset.sum_congr rfl fun i _ => (dropLetter_apply _ _).symm

/-- **The index of the defining sum of `Φ_k`, solved.** A letter-monomial exponent `F` is `x₁^a`
times `e` moved up one letter exactly when its first letter carries the exponent `a` and discarding
that letter leaves `e`. Read left to right this evaluates the index of `HJO.Sym.coeff_insertFront`;
read right to left it says the labellings contributing to the coefficient of `Φ_k F` at `e` are
exactly those grouped by the exponent of their first letter. -/
theorem eq_single_add_mapDomain_succ_iff {F e : ℕ →₀ ℕ} {a : ℕ} :
    F = Finsupp.single 0 a + e.mapDomain Nat.succ ↔ F 0 = a ∧ dropLetter F = e := by
  have hzero : ∀ (b : ℕ) (g : ℕ →₀ ℕ),
      (Finsupp.single 0 b + g.mapDomain Nat.succ : ℕ →₀ ℕ) 0 = b := fun b g => by
    rw [Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.mapDomain_of_notMem_range g 0 (by simp), add_zero]
  have hsucc : ∀ (b n : ℕ) (g : ℕ →₀ ℕ),
      (Finsupp.single 0 b + g.mapDomain Nat.succ : ℕ →₀ ℕ) (n + 1) = g n := fun b n g => by
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (by omega),
      Finsupp.mapDomain_apply Nat.succ_injective, zero_add]
  refine ⟨fun h => ?_, fun ⟨h0, h1⟩ => ?_⟩
  · subst h
    exact ⟨hzero a e, Finsupp.ext fun n => by rw [dropLetter_apply, hsucc a n e]⟩
  · subst h1
    refine Finsupp.ext fun n => ?_
    cases n with
    | zero => rw [h0, hzero]
    | succ m => rw [hsucc, dropLetter_apply]

/-! ### Discarding a letter of a merged variable -/

/-- **Discarding the first letter carries the merged variables of one level to the next**, on the
alphabet exponent: below the level both exponents are `0`; at the level the merged variable *is* the
first letter, which is discarded, and one level up it is the new auxiliary variable and contributes
nothing; and above the level the drop of the letter index cancels the rise of the level. This is the
exponent half of `HJO.Sym.insertFront_zvar`. -/
theorem dropLetter_zvarExponent (k j : ℕ) :
    dropLetter (zvarExponent k j) = zvarExponent (k + 1) j := by
  refine Finsupp.ext fun n => ?_
  rw [dropLetter_apply]
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

/-- **Discarding the first letter carries the merged variables of one level to the next**, on the
coefficient in the auxiliary variables: below the level the coefficient is an auxiliary variable
and is merely renamed; at the level it is `1` below and the new auxiliary variable `y_{k+1}` above,
which is exactly the first letter being absorbed; and above the level both are `1`. This is the
coefficient half of `HJO.Sym.insertFront_zvar`, the exponent of `y_{k+1}` being the exponent of the
first letter that `HJO.Sym.dropLetter` discards. -/
theorem zvarCoeff_succ_level (K : Type*) [CommRing K] (k j : ℕ) :
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

end HJO.Sym

namespace HJO.Dyck

variable {K : Type*} [CommRing K]

/-! ### The free part of a prepended labelling -/

/-- The positions of `E_kπ` at or above the new level are the successors of the positions of `π` at
or above the old one: the prepended position is below the level, and every other position is one
later than the position of `π` it carries. -/
private theorem filter_succ_le_eq_image_succ (k N : ℕ) :
    ({j : Fin (N + 1) | k + 1 ≤ (j : ℕ)} : Finset (Fin (N + 1)))
      = Finset.image Fin.succ ({i : Fin N | k ≤ (i : ℕ)} : Finset (Fin N)) := by
  refine Finset.ext fun j => ?_
  induction j using Fin.cases with
  | zero => simp
  | succ i =>
    rw [mem_filter_univ, Finset.mem_image]
    refine ⟨fun h => ⟨i, mem_filter_univ i |>.2 (by simpa using h), rfl⟩, ?_⟩
    rintro ⟨l, hl, hli⟩
    obtain rfl : l = i := Fin.succ_injective _ hli
    simpa using mem_filter_univ _ |>.1 hl

/-- **Prepending the new special letter discards the first letter of the alphabet exponent** of the
free part of a labelling monomial: the prepended position lies below the new level and contributes
nothing, every other position contributes one level up, and by
`HJO.Sym.dropLetter_zvarExponent` that is the old contribution with its first letter discarded. -/
theorem ztailExponent_prependLabel (k : ℕ) {N : ℕ} (w : Fin N → ℕ) :
    ztailExponent (k + 1) (prependLabel k w) = dropLetter (ztailExponent k w) := by
  rw [ztailExponent, filter_succ_le_eq_image_succ,
    Finset.sum_image fun a _ b _ h => Fin.succ_injective _ h, ztailExponent, dropLetter_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [prependLabel, Fin.cons_succ]
  exact (dropLetter_zvarExponent k (w i)).symm

/-- **Prepending the new special letter multiplies the coefficient of the free part by `y_{k+1}` to
the exponent of the first letter**: the prepended position contributes nothing and every other
position contributes one level up, where by `HJO.Sym.zvarCoeff_succ_level` a letter at the old level
has become the new auxiliary variable. Together with
`HJO.Dyck.ztailExponent_prependLabel` this says `z^{(k+1)}_{E^*_kw,♭} = Φ_k(z^{(k)}_{w,♭})`, the
step through `HJO.Sym.insertFront_zvar`. -/
theorem ztailCoeff_prependLabel (K : Type*) [CommRing K] (k : ℕ) {N : ℕ} (w : Fin N → ℕ) :
    ztailCoeff K (k + 1) (prependLabel k w) =
      MvPolynomial.X (Fin.last k) ^ (ztailExponent k w) 0 *
        MvPolynomial.rename Fin.castSucc (ztailCoeff K k w) := by
  rw [ztailCoeff, filter_succ_le_eq_image_succ,
    Finset.prod_image fun a _ b _ h => Fin.succ_injective _ h, ztailExponent,
    Finsupp.finsetSum_apply, ztailCoeff, map_prod, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [prependLabel, Fin.cons_succ]
  exact zvarCoeff_succ_level K k (w i)

/-- **A labelling of `N` positions contributes at most `N` to the exponent of the first letter** of
its free part: each position contributes `0` or `1` there. This is why no boundedness hypothesis is
needed in `HJO.Dyck.partialCharSeries_prependEast` — the sum defining `Φ_k` on `ν_σ(π)` has support
in `Finset.range (N + 1)`, so the extension by `0` of `HJO.Sym.insertFront` never fires. -/
theorem ztailExponent_apply_zero_le (k : ℕ) {N : ℕ} (w : Fin N → ℕ) :
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

/-! ### The characteristic series after prepending an east step -/

/-- The summand of `ν_{σ^{(k+1)}}(E_kπ)` at a prepended labelling, in terms of the summand of
`ν_{Id_k}(π)`: the inversion count rises by `k` and the monomial is carried by `Φ_k`. -/
private theorem smul_ztailCoeff_prependLabel (q : K) {k N : ℕ} (x : Fin N → ℕ) (hk : k ≤ N)
    {w : Fin N → ℕ} (hw : ∀ i : Fin N, (i : ℕ) < k → w i = (i : ℕ)) :
    q ^ #(invSet (finPairs (N + 1) (attackSet (prependEast k x))) (prependLabel k w)) •
        ztailCoeff K (k + 1) (prependLabel k w) =
      q ^ k • (MvPolynomial.X (Fin.last k) ^ (ztailExponent k w) 0 *
        MvPolynomial.rename Fin.castSucc
          (q ^ #(invSet (finPairs N (attackSet x)) w) • ztailCoeff K k w)) := by
  have hinv : #(invSet (finPairs (N + 1) (attackSet (prependEast k x))) (prependLabel k w))
      = k + #(invSet (finPairs N (attackSet x)) w) := by
    exact (invNumber_prependEast_prependLabel x hk hw).trans (Nat.add_comm _ k)
  rw [ztailCoeff_prependLabel, hinv, map_smul, mul_smul_comm, smul_smul, ← pow_add]

/-- **The characteristic series after prepending an east step**:

`ν_{σ^{(k+1)}}(E_kπ) = q^k Φ_k(ν_{Id_k}(π))`.

Prepending the new special letter is a bijection from the labellings of `π` prescribed by `Id_k`
onto the labellings of `E_kπ` prescribed by `σ^{(k+1)}`
(`HJO.Dyck.bijOn_prependLabel_noAttackLabellings`), it costs exactly `k` inversions
(`HJO.Dyck.invNumber_prependEast_prependLabel`), and it carries the free part of the labelling
monomial to its image under the insertion (`HJO.Dyck.ztailExponent_prependLabel` and
`HJO.Dyck.ztailCoeff_prependLabel`). Summing, the coefficient of the left side at a letter-monomial
`e` is `q^k` times the coefficient of `Φ_k(ν_{Id_k}(π))` there, the labellings being grouped by the
exponent their free part carries at the first letter.

The `π ∈ 𝔻_{k,N}` is weakened to `k ≤ N`, the only part of it any input uses. No
boundedness hypothesis is needed for the insertion, although `HJO.Sym.insertFront` is only the total
extension by `0` of the `Φ_k`: by `HJO.Dyck.ztailExponent_apply_zero_le` the sum
defining it on `ν_{Id_k}(π)` is supported in `Finset.range (N + 1)`, so the extension never fires
here. -/
@[hjo "lem_cm_nu_east"]
theorem partialCharSeries_prependEast (q : K) {k N : ℕ} (x : Fin N → ℕ) (hk : k ≤ N) :
    partialCharSeries q (k + 1) (prependEast k x) (cycleTuple (Fin.last k)) =
      q ^ k • insertFront K k (partialCharSeries q k x (identityTuple k)) := by
  refine MvPowerSeries.ext fun e => ?_
  -- The finite set of letters bounding the labellings on both sides.
  have hmemA : ∀ j : ℕ, j < k + 1 →
      j ∈ Finset.range (k + 1) ∪ (e.support.image Nat.succ).image (· + k) := fun j hj =>
    Finset.mem_union_left _ (Finset.mem_range.2 hj)
  have hmemB : ∀ n : ℕ, e n ≠ 0 →
      n + 1 + k ∈ Finset.range (k + 1) ∪ (e.support.image Nat.succ).image (· + k) := fun n hn =>
    Finset.mem_union_right _
      (Finset.mem_image.2 ⟨n + 1, Finset.mem_image.2 ⟨n, Finsupp.mem_support_iff.2 hn, rfl⟩, rfl⟩)
  -- The index of the defining sum of the insertion, solved once and for all.
  have hE : ∀ a : ℕ, (Finsupp.single 0 a + e.mapDomain Nat.succ : ℕ →₀ ℕ) 0 = a ∧
      dropLetter (Finsupp.single 0 a + e.mapDomain Nat.succ : ℕ →₀ ℕ) = e := fun a =>
    eq_single_add_mapDomain_succ_iff.1 rfl
  -- The letters of a labelling of `E_kπ` contributing to the coefficient at `e`.
  have hsubL : nuLetters (k + 1) e (cycleTuple (Fin.last k)) ⊆
      Finset.range (k + 1) ∪ (e.support.image Nat.succ).image (· + k) := by
    intro j hj
    rw [nuLetters, Finset.mem_union, Finset.mem_union] at hj
    rcases hj with (hj | hj) | hj
    · exact hmemA j (Finset.mem_range.1 hj)
    · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hj
      have h1 := hmemB n (Finsupp.mem_support_iff.1 hn)
      rwa [show n + 1 + k = n + (k + 1) by omega] at h1
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hj
      exact hmemA _ (cycleTuple_lt _ i)
  -- The letters of a labelling of `π` contributing to the coefficient at `x₁^a` times `e` raised.
  have hsubR : ∀ a : ℕ,
      nuLetters k (Finsupp.single 0 a + e.mapDomain Nat.succ) (identityTuple k) ⊆
        Finset.range (k + 1) ∪ (e.support.image Nat.succ).image (· + k) := by
    intro a j hj
    rw [nuLetters, Finset.mem_union, Finset.mem_union] at hj
    rcases hj with (hj | hj) | hj
    · exact hmemA j (by have := Finset.mem_range.1 hj; omega)
    · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hj
      cases m with
      | zero => exact hmemA _ (by omega)
      | succ n =>
        refine hmemB n ?_
        have h1 := Finsupp.mem_support_iff.1 hm
        rwa [← dropLetter_apply, (hE a).2] at h1
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hj
      exact hmemA _ (by have := identityTuple_lt k i; omega)
  -- The coefficients of `ν_{Id_k}(π)` at a high power of the first letter vanish.
  have hvan : ∀ a : ℕ, N < a → MvPowerSeries.coeff (Finsupp.single 0 a + e.mapDomain Nat.succ)
      (partialCharSeries q k x (identityTuple k)) = 0 := by
    intro a ha
    rw [coeff_partialCharSeries]
    refine Finset.sum_eq_zero fun w hw => ?_
    exfalso
    have h1 := ztailExponent_apply_zero_le k w
    rw [(Finset.mem_filter.1 hw).2.2, (hE a).1] at h1
    omega
  -- The right-hand side, coefficientwise: a finite sum over the exponent of the first letter.
  have hstep3 : MvPowerSeries.coeff e
        (q ^ k • insertFront K k (partialCharSeries q k x (identityTuple k)))
      = q ^ k • ∑ a ∈ Finset.range (N + 1), MvPolynomial.X (Fin.last k) ^ a *
          MvPolynomial.rename Fin.castSucc (MvPowerSeries.coeff
            (Finsupp.single 0 a + e.mapDomain Nat.succ)
            (partialCharSeries q k x (identityTuple k))) := by
    have h1 : MvPowerSeries.coeff e
          (q ^ k • insertFront K k (partialCharSeries q k x (identityTuple k)))
        = q ^ k • MvPowerSeries.coeff e
          (insertFront K k (partialCharSeries q k x (identityTuple k))) := rfl
    rw [h1, coeff_insertFront]
    congr 1
    refine finsum_eq_sum_of_support_subset _ fun a ha => ?_
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hcon
    exact ha (by simp only [hvan a (by omega : N < a), map_zero, mul_zero])
  -- The left-hand side, coefficientwise: the labellings of `π`, grouped by that exponent.
  have hstep2 : ∑ w ∈ {w ∈ Fintype.piFinset fun _ : Fin N =>
        Finset.range (k + 1) ∪ (e.support.image Nat.succ).image (· + k) |
          w ∈ noAttackLabellings x (identityTuple k) ∧ dropLetter (ztailExponent k w) = e},
        q ^ k • (MvPolynomial.X (Fin.last k) ^ (ztailExponent k w) 0 *
          MvPolynomial.rename Fin.castSucc
            (q ^ #(invSet (finPairs N (attackSet x)) w) • ztailCoeff K k w))
      = q ^ k • ∑ a ∈ Finset.range (N + 1), MvPolynomial.X (Fin.last k) ^ a *
          MvPolynomial.rename Fin.castSucc (MvPowerSeries.coeff
            (Finsupp.single 0 a + e.mapDomain Nat.succ)
            (partialCharSeries q k x (identityTuple k))) := by
    rw [← Finset.smul_sum]
    congr 1
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun w : Fin N → ℕ => (ztailExponent k w) 0)
      (t := Finset.range (N + 1)) fun w _ => Finset.mem_range.2
        (Nat.lt_succ_of_le (ztailExponent_apply_zero_le k w))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coeff_partialCharSeries_of_subset (hsubR a), map_sum, Finset.mul_sum]
    refine Finset.sum_congr (Finset.ext fun w => ?_) fun w hw => ?_
    · simp only [Finset.mem_filter]
      refine ⟨fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, eq_single_add_mapDomain_succ_iff.2 ⟨h4, h3⟩⟩,
        fun ⟨h1, h2, h3⟩ => ?_⟩
      obtain ⟨h4, h5⟩ := eq_single_add_mapDomain_succ_iff.1 h3
      exact ⟨⟨h1, h2, h5⟩, h4⟩
    · rw [(Finset.mem_filter.1 hw).2.2, (hE a).1]
  rw [coeff_partialCharSeries_of_subset hsubL, hstep3]
  refine Eq.trans ?_ hstep2
  refine (Finset.sum_nbij' (prependLabel k) (fun w' => Fin.tail w') ?_ ?_ ?_ ?_ ?_).symm
  -- The bijection maps the labellings of `π` to the labellings of `E_kπ`.
  · intro w hw
    obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hw
    rw [Fintype.mem_piFinset] at h1
    refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun p => ?_,
      (bijOn_prependLabel_noAttackLabellings x).mapsTo h2, ?_⟩
    · induction p using Fin.cases with
      | zero =>
        rw [show prependLabel k w 0 = k by simp]
        exact hmemA k (by omega)
      | succ i =>
        rw [show prependLabel k w i.succ = w i by simp]
        exact h1 i
    · rw [ztailExponent_prependLabel]; exact h3
  -- Its inverse maps back.
  · intro w' hw'
    obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hw'
    rw [Fintype.mem_piFinset] at h1
    obtain ⟨w, hw, hwe⟩ := (bijOn_prependLabel_noAttackLabellings x).surjOn h2
    obtain rfl : Fin.tail w' = w := by rw [← hwe]; simp
    refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => h1 i.succ, hw, ?_⟩
    rw [← ztailExponent_prependLabel, hwe]
    exact h3
  -- The two maps are mutually inverse on the two index sets.
  · exact fun w _ => by simp
  · intro w' hw'
    have h0 : w' 0 = k := by
      rw [eq_of_mem_noAttackLabellings (Finset.mem_filter.1 hw').2.1 (i := 0) (j := 0) rfl,
        cycleTuple_zero]
      exact Fin.val_last k
    have h1 : Fin.cons (w' 0) (Fin.tail w') = w' := Fin.cons_self_tail w'
    rw [h0] at h1
    exact h1
  -- The summands agree.
  · intro w hw
    exact (smul_ztailCoeff_prependLabel q x hk fun i hi =>
      eq_of_mem_noAttackLabellings (Finset.mem_filter.1 hw).2.1 (j := ⟨(i : ℕ), hi⟩) rfl).symm

end HJO.Dyck
