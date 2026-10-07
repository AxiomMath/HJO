/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.ChiPrimeSwap
public import HJO.CarlssonMellit.ChiPrimeZGraded
public import HJO.CarlssonMellit.ZDeltaSums
public import HJO.CarlssonMellit.ZvarMerged
public meta import HJO.Attr

/-! # The swapping operators in the free variables

`HJO.Dyck.isZDelta_auxToFrac_unnormalisedCharSeries`: for a partial Dyck path `π ∈ 𝔻_{k+1,N}`, a
prescription `σ` with pairwise distinct entries having the entry `k + r` and having the entry
`k + r + 1` — if at all — only later,

`χ'_{τ_m σ}(π) = Δ_m(χ'_σ(π))` at `m = k + r`,

stated as the relation `HJO.Sym.IsZDelta`, which is that identity cleared of
its denominator and is where the whole `Δ_m` layer is written.

This is the case `HJO.Dyck.auxToFrac_unnormalisedCharSeries_transposeTuple` excludes. There both
interchanged variables are auxiliary, the division takes place in `𝕂(y_1, …, y_{k+1})` and a class
contributes to a single coefficient of the alphabet. Here `m ≥ k`, so one of the two interchanged
variables is a *letter*; the interchange `ŝ_m` is not a substitution of `P°_{k+1}`, `Δ_m` is the
operator the merged grading of `HJO.Sym.zGraded` supplies, and a class spans infinitely many
monomials of the alphabet — so the passage from the classes to the series is a genuinely
monomialwise sum and needs `HJO.Sym.isZDelta_summableSum`.

## Main results

* `HJO.Dyck.isZDelta_auxToFrac_finsum_labelClass`: the per-class step. `Δ_m` carries the class sum
  of `w` for `σ` to the class sum of `τ_m w` for `τ_m σ`.
* `HJO.Dyck.isZDelta_auxToFrac_unnormalisedCharSeries`: the main statement.

## Implementation notes

*The classes are indexed by their key, and grouped by merged degree.* A class is determined by
`HJO.Dyck.labelClassKey`, so the classes of merged degree `d` are indexed by tuples `c`: the
`HJO.Dyck.keyClass` of `c` is the class of any of its members, and is empty when `c` is not a key.
`HJO.Dyck.classPart` is the corresponding class sum, and `HJO.Dyck.summableSum_classPart` says the
monomialwise sum of those is the part `HJO.Dyck.unnormalisedCharPart` of merged degree `d` — the
grouping of the defining sum of `HJO.Dyck.unnormalisedCharSeries` by the classes, one coefficient at
a time. The key is untouched by `τ_m`, so the same index set serves both prescriptions, which is
what makes `HJO.Sym.isZDelta_summableSum` applicable with the two families paired index by index.

*The merged degree is constant on a class, including at `r = 0`.* Members of a class agree off the
two-letter support and carry `m` or `m + 1` on it, and both of those are at least `k`, so
`HJO.Dyck.mergedDegree` — the count of positions whose letter lies in the merged alphabet, which is
what `HJO.Sym.zGraded` grades by — does not move. At `r = 0` one of the two letters is the
distinguished merged letter `y_{k+1}`, below the level of the *alphabet*; it is nevertheless counted
by `mergedDegree`, which is why the asserted homogeneity is true in this indexing and
would be false for the alphabet degree alone.

*The invariant factor is handled by the subring `HJO.Sym.zSwapFixedSubring`.* The proof checks
factor by factor that `q^e g ∏_{t≥2}(a_m(l_t,0)+a_m(l_t,1))` is fixed by `ŝ_m`; since `ŝ_m` is a
ring automorphism of `Z^{(k+1)}` those elements form a subring, and the check is three membership
facts closed under products and powers. `HJO.CarlssonMellit.ZvarMerged` is the dictionary
turning the class-sum layer's merged variables and run weights into the letters and run weights the
operator statements are written at.

*The `N ≥ k` and `k ≥ 1` are not binders.* The first is
`HJO.Dyck.IsPartialDyck.le_length`, and the second is carried by the level `k + 1`. Pairwise
distinctness of `σ` is kept: it is what makes the first position of the two-letter support be the
position of `m`, hence what forces the first bit. The hypothesis on `m` is carried as
`m = k + r` with `r : ℕ`, which is the `m ≥ k` with no truncated subtraction.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Proposition 4.8.
-/

@[expose] public section

open Finset

namespace HJO.Dyck

open HJO.Sym

variable {K : Type*} [CommRing K] {N k m d : ℕ} {x : Fin N → ℕ} {σ : Fin (k + 1) → ℕ}
  {w c : Fin N → ℕ} {e : ℕ →₀ ℕ}

/-! ### The merged degree is constant on a class -/

/-- The merged degree reads only which letters lie at or above `k`. -/
private theorem mergedDegree_congr {w w' : Fin N → ℕ} (h : ∀ i : Fin N, k ≤ w' i ↔ k ≤ w i) :
    mergedDegree k w' = mergedDegree k w := by
  simp only [mergedDegree]
  exact congrArg Finset.card (Finset.filter_congr fun i _ => h i)

/-- **The merged degree is constant on a class**, both special letters lying at or above the level:
inside the two-letter support every member carries `m` or `m + 1`, and outside it the members
agree. This is the homogeneity the summation over the classes needs. -/
private theorem mergedDegree_eq_of_mem_labelClass {w' : Fin N → ℕ} (hkm : k ≤ m)
    (h : w' ∈ labelClass x σ m w) : mergedDegree k w' = mergedDegree k w := by
  refine mergedDegree_congr fun i => ?_
  by_cases hi : (i : ℕ) ∈ labelSupport m w
  · have hi' : (i : ℕ) ∈ labelSupport m w' := by rw [h.2.1]; exact hi
    have h1 : k ≤ w' i := by
      rcases mem_labelSupport_val.1 hi' with h1 | h1 <;> omega
    have h2 : k ≤ w i := by
      rcases mem_labelSupport_val.1 hi with h2 | h2 <;> omega
    exact iff_of_true h1 h2
  · rw [h.2.2 i hi]

/-- The relabelling does not move the merged degree, both special letters lying at or above the
level. -/
private theorem mergedDegree_transposeTuple (hkm : k ≤ m) (w : Fin N → ℕ) :
    mergedDegree k (transposeTuple m w) = mergedDegree k w := by
  refine mergedDegree_congr fun i => ?_
  rw [transposeTuple_apply]
  rcases eq_or_ne (w i) m with h | h
  · rw [h, Equiv.swap_apply_left]
    exact iff_of_true (by omega) (by omega)
  rcases eq_or_ne (w i) (m + 1) with h' | h'
  · rw [h', Equiv.swap_apply_right]
    exact iff_of_true (by omega) (by omega)
  · rw [swap_succ_of_ne h h']

/-! ### The classes of one merged degree, indexed by their key -/

/-- The class of the key `c` in merged degree `d`: the no-attack labellings of merged degree `d`
whose `HJO.Dyck.labelClassKey` is `c`. It is a class of `HJO.Dyck.labelClass` when it is nonempty,
and empty when `c` is not a key. -/
private def keyClass (x : Fin N → ℕ) (σ : Fin (k + 1) → ℕ) (m d : ℕ) (c : Fin N → ℕ) :
    Set (Fin N → ℕ) :=
  {w | w ∈ noAttackLabellings x σ ∧ labelClassKey m w = c ∧ mergedDegree k w = d}

private theorem mem_keyClass : w ∈ keyClass x σ m d c ↔ w ∈ noAttackLabellings x σ ∧
    labelClassKey m w = c ∧ mergedDegree k w = d :=
  Iff.rfl

/-- A key class is finite: at each position its members carry `m`, `m + 1`, or the letter the key
records. -/
private theorem keyClass_finite (x : Fin N → ℕ) (σ : Fin (k + 1) → ℕ) (m d : ℕ) (c : Fin N → ℕ) :
    (keyClass x σ m d c).Finite := by
  classical
  refine Set.Finite.subset (Fintype.piFinset fun _ : Fin N =>
    ({m, m + 1} ∪ Finset.image c Finset.univ : Finset ℕ)).finite_toSet fun v hv => ?_
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro i
  have hi := congrFun (mem_keyClass.1 hv).2.1 i
  rw [labelClassKey] at hi
  by_cases h : v i = m ∨ v i = m + 1
  · rcases h with h | h <;> simp [h]
  · rw [ite_eq_right h] at hi
    exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_univ i, hi.symm⟩)

/-- **A nonempty key class is the class of any of its members.** The key determines the class by
`HJO.Dyck.labelClassKey_eq_iff`, and the merged degree is constant on a class. -/
private theorem keyClass_eq_labelClass (hkm : k ≤ m) (hw : w ∈ keyClass x σ m d c) :
    keyClass x σ m d c = labelClass x σ m w := by
  obtain ⟨-, hwkey, hwd⟩ := mem_keyClass.1 hw
  refine Set.ext fun v => ⟨fun hv => ?_, fun hv => ?_⟩
  · obtain ⟨hvna, hvkey, -⟩ := mem_keyClass.1 hv
    exact mem_labelClass.2 ⟨hvna, labelClassKey_eq_iff.1 (hvkey.trans hwkey.symm)⟩
  · obtain ⟨hvna, hS, hf⟩ := mem_labelClass.1 hv
    exact mem_keyClass.2 ⟨hvna, (labelClassKey_eq_iff.2 ⟨hS, hf⟩).trans hwkey,
      (mergedDegree_eq_of_mem_labelClass hkm hv).trans hwd⟩

/-- The relabelling carries the key class of `c` for `σ` into the key class of the same `c` for
`τ_m σ`: it leaves the key and the merged degree alone. -/
private theorem transposeTuple_mem_keyClass (hkm : k ≤ m) (hw : w ∈ keyClass x σ m d c) :
    transposeTuple m w ∈ keyClass x (transposeTuple m σ) m d c := by
  obtain ⟨hna, hkey, hd⟩ := mem_keyClass.1 hw
  refine mem_keyClass.2 ⟨(bijOn_transposeTuple x σ m).mapsTo hna, ?_, ?_⟩
  · rw [labelClassKey_transposeTuple]; exact hkey
  · rw [mergedDegree_transposeTuple hkm]; exact hd

/-! ### The class sums of one merged degree -/

/-- The sum of `q^{inv} z^{(k+1)}_{w'}` over the key class of `c` in merged degree `d`: the class
sum of `HJO.Dyck.finsum_labelClass` when the key class is a class, and `0` otherwise. -/
private noncomputable def classPart (q : K) (x : Fin N → ℕ) (σ : Fin (k + 1) → ℕ) (m d : ℕ)
    (c : Fin N → ℕ) : AuxAlphabetSeries K (k + 1) :=
  ∑ᶠ v ∈ keyClass x σ m d c,
    scalarSeries K (k + 1) q ^ invNumber (attackSet x) (wordOfFin v) * zmon K (k + 1) v

/-- The labellings of merged degree `d` contributing to the coefficient of `x^e`: the index set of
`HJO.Dyck.unnormalisedCharPart`, named so that the grouping into classes can be stated. -/
private noncomputable def partIndex (x : Fin N → ℕ) (σ : Fin (k + 1) → ℕ) (d : ℕ) (e : ℕ →₀ ℕ) :
    Finset (Fin N → ℕ) :=
  {v ∈ {v ∈ Fintype.piFinset fun _ : Fin N => zmonLetters (k + 1) e |
      v ∈ noAttackLabellings x σ ∧ zmonExponent (k + 1) v = e} | mergedDegree k v = d}

private theorem mem_partIndex {v : Fin N → ℕ} : v ∈ partIndex x σ d e ↔
    v ∈ noAttackLabellings x σ ∧ zmonExponent (k + 1) v = e ∧ mergedDegree k v = d := by
  simp only [partIndex, Finset.mem_filter, Fintype.mem_piFinset]
  exact ⟨fun h => ⟨h.1.2.1, h.1.2.2, h.2⟩,
    fun h => ⟨⟨fun i => mem_zmonLetters h.2.1 i, h.1, h.2.1⟩, h.2.2⟩⟩

variable {q : K}

private theorem coeff_unnormalisedCharPart_partIndex :
    MvPowerSeries.coeff e (unnormalisedCharPart q k x σ d) =
      ∑ v ∈ partIndex x σ d e,
        q ^ #(invSet (finPairs N (attackSet x)) v) • zmonCoeff K (k + 1) v := by
  rw [coeff_unnormalisedCharPart, partIndex]
  exact Finset.sum_congr (Finset.ext fun v => by simp only [Finset.mem_filter]) fun _ _ => rfl

/-- **The coefficient of a class sum**: the labellings of the key class whose monomial has alphabet
exponent `e` are exactly the fibre of the key at `c` inside the index set of that coefficient. -/
private theorem coeff_classPart (q : K) (x : Fin N → ℕ) (σ : Fin (k + 1) → ℕ) (m d : ℕ)
    (c : Fin N → ℕ) (e : ℕ →₀ ℕ) :
    MvPowerSeries.coeff e (classPart q x σ m d c) =
      ∑ v ∈ {v ∈ partIndex x σ d e | labelClassKey m v = c},
        q ^ #(invSet (finPairs N (attackSet x)) v) • zmonCoeff K (k + 1) v := by
  classical
  have hsub : {v ∈ partIndex x σ d e | labelClassKey m v = c}
      ⊆ (keyClass_finite x σ m d c).toFinset := fun v hv => by
    obtain ⟨hv1, hv2⟩ := Finset.mem_filter.1 hv
    obtain ⟨hna, -, hvd⟩ := mem_partIndex.1 hv1
    exact (Set.Finite.mem_toFinset _).2 (mem_keyClass.2 ⟨hna, hv2, hvd⟩)
  have hzero : ∀ v ∈ (keyClass_finite x σ m d c).toFinset,
      v ∉ {v ∈ partIndex x σ d e | labelClassKey m v = c} →
      MvPowerSeries.coeff e (scalarSeries K (k + 1) q ^ invNumber (attackSet x) (wordOfFin v)
        * zmon K (k + 1) v) = 0 := fun v hv hvn => by
    obtain ⟨hna, hkey, hvd⟩ := mem_keyClass.1 ((Set.Finite.mem_toFinset _).1 hv)
    have hne : ¬ e = zmonExponent (k + 1) v := fun hce =>
      hvn (Finset.mem_filter.2 ⟨mem_partIndex.2 ⟨hna, hce.symm, hvd⟩, hkey⟩)
    rw [← card_invSet_finPairs_attackSet, scalarSeries_pow_mul_zmon,
      MvPowerSeries.coeff_monomial, ite_eq_right hne]
  rw [classPart, finsum_mem_eq_finite_toFinset_sum _ (keyClass_finite x σ m d c), map_sum,
    ← Finset.sum_subset hsub hzero]
  refine Finset.sum_congr rfl fun v hv => ?_
  obtain ⟨-, hve, -⟩ := mem_partIndex.1 (Finset.mem_filter.1 hv).1
  rw [← card_invSet_finPairs_attackSet, scalarSeries_pow_mul_zmon, hve,
    MvPowerSeries.coeff_monomial_same]

/-- Only the keys of the labellings reaching a coefficient contribute to it there. -/
private theorem mem_image_labelClassKey_of_coeff_ne_zero (q : K) (x : Fin N → ℕ)
    (σ : Fin (k + 1) → ℕ) (m d : ℕ) (c : Fin N → ℕ) (e : ℕ →₀ ℕ)
    (hc : MvPowerSeries.coeff e (classPart q x σ m d c) ≠ 0) :
    c ∈ (partIndex x σ d e).image (labelClassKey m) := by
  classical
  by_contra hcon
  refine hc ?_
  rw [coeff_classPart]
  refine Finset.sum_eq_zero fun v hv => ?_
  exact absurd (Finset.mem_image.2 ⟨v, (Finset.mem_filter.1 hv).1, (Finset.mem_filter.1 hv).2⟩) hcon

/-- The family of class sums of one merged degree is monomialwise finite: at each monomial only the
keys of the finitely many labellings reaching it contribute. -/
private theorem isSummableFamily_classPart (q : K) (x : Fin N → ℕ) (σ : Fin (k + 1) → ℕ)
    (m d : ℕ) : IsSummableFamily (classPart q x σ m d) := by
  classical
  refine pointwiseFinite_of_forall_exists_finset fun e =>
    ⟨(partIndex x σ d e).image (labelClassKey m), fun c hc => ?_⟩
  exact mem_image_labelClassKey_of_coeff_ne_zero q x σ m d c e hc

/-- **The class sums of merged degree `d` sum to the part of merged degree `d`.** This is the
grouping of the sum of `HJO.Dyck.unnormalisedCharSeries` into the classes of
`HJO.Dyck.equivalence_labelClass`, read one coefficient at a time: each coefficient is a finite sum
over `HJO.Dyck.partIndex`, and grouping it by `HJO.Dyck.labelClassKey` splits it into the
contributions of the classes. -/
private theorem summableSum_classPart (q : K) (x : Fin N → ℕ) (σ : Fin (k + 1) → ℕ) (m d : ℕ) :
    summableSum (classPart q x σ m d) = unnormalisedCharPart q k x σ d := by
  classical
  refine MvPowerSeries.ext fun e => ?_
  rw [coeff_summableSum_eq_sum
      (fun c hc => mem_image_labelClassKey_of_coeff_ne_zero q x σ m d c e hc),
    coeff_unnormalisedCharPart_partIndex,
    Finset.sum_congr rfl fun c _ => coeff_classPart q x σ m d c e]
  exact Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image_of_mem _ hv) _

/-- The family of class sums, pushed into `P°_{k+1}`, is monomialwise finite. -/
private theorem isSummableFamily_auxToFrac_classPart (q : K) (x : Fin N → ℕ)
    (σ : Fin (k + 1) → ℕ) (m d : ℕ) :
    IsSummableFamily fun c => auxToFrac K (k + 1) (classPart q x σ m d c) :=
  (isSummableFamily_classPart q x σ m d).map
    (algebraMap (MvPolynomial (Fin (k + 1)) K) (AuxFrac K (k + 1))).toAddMonoidHom
    fun F e => coeff_auxToFrac (k + 1) F e

/-- The part of merged degree `d`, in `P°_{k+1}`, is the monomialwise sum of the class sums. -/
private theorem auxToFrac_unnormalisedCharPart_eq (q : K) (x : Fin N → ℕ) (σ : Fin (k + 1) → ℕ)
    (m d : ℕ) : auxToFrac K (k + 1) (unnormalisedCharPart q k x σ d)
      = summableSum fun c => auxToFrac K (k + 1) (classPart q x σ m d c) := by
  rw [← summableSum_classPart q x σ m d]
  exact map_summableSum (isSummableFamily_classPart q x σ m d)
    (algebraMap (MvPolynomial (Fin (k + 1)) K) (AuxFrac K (k + 1))).toAddMonoidHom
    fun F e => coeff_auxToFrac (k + 1) F e

variable [IsDomain K]

/-- **A class sum of merged degree `d` lies in `Z^{(k+1)}_d`.** Its coefficient at a
letter-monomial `x^α` is a sum over labellings that all share the alphabet exponent `α` and the
merged degree `d`, hence by `HJO.Dyck.mergedDegree_eq_lastAuxDegree_add_degree` also the exponent of
the distinguished letter; above the degree the same identity empties the sum. This is
`HJO.Dyck.auxToFrac_unnormalisedCharPart_mem_zGraded` read on one class. -/
private theorem auxToFrac_classPart_mem_zGraded (q : K) (x : Fin N → ℕ) (σ : Fin (k + 1) → ℕ)
    (m d : ℕ) (c : Fin N → ℕ) :
    auxToFrac K (k + 1) (classPart q x σ m d c) ∈ zGraded K k d := by
  classical
  refine ⟨fun α b hb => ?_, fun α hα => ?_⟩
  · rw [← mem_auxFracYPow, coeff_auxToFrac, coeff_classPart, map_sum]
    refine sum_mem fun v hv => ?_
    obtain ⟨-, hve, hvd⟩ := mem_partIndex.1 (Finset.mem_filter.1 hv).1
    have hsplit := mergedDegree_eq_lastAuxDegree_add_degree k v
    rw [hve] at hsplit
    have hb' : lastAuxDegree k v = b := by omega
    refine mem_auxFracYPow.2 ⟨algebraMap (MvPolynomial (Fin k) K) (AuxFrac K k)
      (q ^ #(invSet (finPairs N (attackSet x)) v) • zmonCoeff K k v), ?_⟩
    rw [auxFracCastSucc_algebraMap, yFrac, ← map_pow, ← map_mul]
    congr 1
    rw [map_smul, smul_mul_assoc, zmonCoeff_succ, hb']
  · have h0 : MvPowerSeries.coeff α (classPart q x σ m d c) = 0 := by
      rw [coeff_classPart]
      refine Finset.sum_eq_zero fun v hv => ?_
      obtain ⟨-, hve, hvd⟩ := mem_partIndex.1 (Finset.mem_filter.1 hv).1
      have hsplit := mergedDegree_eq_lastAuxDegree_add_degree k v
      rw [hve] at hsplit
      omega
    rw [coeff_auxToFrac, h0, map_zero]

/-! ### The first position of the support, with `m + 1` possibly absent -/

/-- **The first position of the two-letter support is the position of the letter `m`**, when `σ` has
pairwise distinct entries, has the entry `m` at the position `a`, and has the entry `m + 1` — if at
all — only after `a`. Below the level the support consists of the positions carrying `m` and
`m + 1`, and no such position precedes `a`.

This is `HJO.Dyck.sortNth_one_eq_of_special` with the reading of `σ^{-1}(m + 1)` as `∞`
when `m + 1` is not an entry, which is exactly what is needed at `m ≥ k`: the entries below the
level are `0, …, k`, so `m + 1` need not occur. -/
private theorem sortNth_one_eq_of_entry {k : ℕ} {σ : Fin k → ℕ} (hx : IsPartialDyck k N x)
    (hw : w ∈ noAttackLabellings x σ) (hσ : Function.Injective σ) {a : Fin k} (ha : σ a = m)
    (hb : ∀ b : Fin k, σ b = m + 1 → (a : ℕ) < (b : ℕ)) :
    sortNth (labelSupport m w) 1 = (a : ℕ) := by
  have hak : (a : ℕ) < k := a.isLt
  have hwa : wordOfFin w (a : ℕ) = m := by
    rw [wordOfFin_eq_of_lt_level hx.le_length hw hak]
    simpa using ha
  have haS : (a : ℕ) ∈ labelSupport m w :=
    mem_labelSupport.2 ⟨lt_of_lt_of_le hak hx.le_length, Or.inl hwa⟩
  have hp : 1 ≤ #(labelSupport m w) := Finset.card_pos.2 ⟨_, haS⟩
  have hmem : sortNth (labelSupport m w) 1 ∈ labelSupport m w := sortNth_mem le_rfl hp
  obtain ⟨t, ht1, htp, hteq⟩ := exists_sortNth haS
  have hle : sortNth (labelSupport m w) 1 ≤ (a : ℕ) :=
    hteq ▸ sortNth_le_sortNth le_rfl htp ht1
  refine le_antisymm hle ?_
  by_contra hcon
  have hck : sortNth (labelSupport m w) 1 < k := lt_trans (by omega) hak
  have hval := wordOfFin_eq_of_lt_level hx.le_length hw hck
  rcases wordOfFin_eq_or_eq_of_mem_labelSupport hmem with h | h
  · rw [hval] at h
    have h2 := congrArg Fin.val (hσ (h.trans ha.symm))
    simp only at h2
    omega
  · rw [hval] at h
    have h2 : (a : ℕ) < sortNth (labelSupport m w) 1 := hb ⟨_, hck⟩ h
    omega

/-! ### The per-class step -/

/-- The algebra of the per-class step: `Δ_m` pulls out a factor its interchange fixes, and moves the
one factor that is left. -/
private theorem isZDelta_auxToFrac_mul_mul {q : K} {r : ℕ}
    (Q G P A₀ A₁ : AuxAlphabetSeries K (k + 1))
    (hQ : auxToFrac K (k + 1) Q ∈ zSwapFixedSubring K k r)
    (hG : auxToFrac K (k + 1) G ∈ zSwapFixedSubring K k r)
    (hP : auxToFrac K (k + 1) P ∈ zSwapFixedSubring K k r)
    (hAm : auxToFrac K (k + 1) A₀ ∈ zRing K k)
    (hA : IsZDelta q r (auxToFrac K (k + 1) A₀) (auxToFrac K (k + 1) A₁)) :
    IsZDelta q r (auxToFrac K (k + 1) (Q * G * (A₀ * P)))
      (auxToFrac K (k + 1) (Q * G * (A₁ * P))) := by
  have hg := mem_zSwapFixedSubring.1 (mul_mem (mul_mem hQ hG) hP)
  rw [show auxToFrac K (k + 1) (Q * G * (A₀ * P)) = auxToFrac K (k + 1) Q * auxToFrac K (k + 1) G
        * auxToFrac K (k + 1) P * auxToFrac K (k + 1) A₀ from by
      rw [map_mul, map_mul, map_mul]; ring,
    show auxToFrac K (k + 1) (Q * G * (A₁ * P)) = auxToFrac K (k + 1) Q * auxToFrac K (k + 1) G
        * auxToFrac K (k + 1) P * auxToFrac K (k + 1) A₁ from by
      rw [map_mul, map_mul, map_mul]; ring]
  exact isZDelta_mul_of_zSwap_eq hAm hg.1 hg.2 hA

/-- The weight of a run at two letters of the merged alphabet lies in `Z^{(k+1)}`, being a product
of powers of elements that do. -/
private theorem runWeight_zLetter_mem_zRing (q : K) (r l : ℕ) (ε : Bool) :
    runWeight (MvPowerSeries.C (scalarFrac K q) : AuxAlphabetSeriesFrac K (k + 1))
        (zLetterSeries K k r) (zLetterSeries K k (r + 1)) l ε ∈ zRing K k := by
  have hq : (MvPowerSeries.C (scalarFrac K q) : AuxAlphabetSeriesFrac K (k + 1)) ∈ zRing K k :=
    zGraded_subset_zRing K k 0 (C_scalarFrac_mem_zGraded q)
  rw [← coe_runWeight (⟨_, hq⟩ : zSubring K k) ⟨_, zLetterSeries_mem_zRing r⟩
    ⟨_, zLetterSeries_mem_zRing (r + 1)⟩ l ε]
  exact (runWeight (⟨_, hq⟩ : zSubring K k) ⟨_, zLetterSeries_mem_zRing r⟩
    ⟨_, zLetterSeries_mem_zRing (r + 1)⟩ l ε).2

/-- **`Δ_m` carries the class sum of `w` for `σ` to the class sum of `τ_m w` for `τ_m σ`**, at
`m = k + r`. Both class sums are given by `HJO.Dyck.finsum_labelClass`, and they differ in exactly
one factor: the weight of the first run, which `w` starts with `m` — that is the hypothesis
`σ^{-1}(m) < σ^{-1}(m+1)`, read with `σ^{-1}(m+1) = ∞` when `m + 1` is not an entry — and `τ_m w`
starts with `m + 1`. Everything else is fixed by `ŝ_m`: the power of `q` is a scalar, each factor of
`g` is a merged variable other than the two that `ŝ_m` interchanges, and the later runs contribute
the symmetric sums of `HJO.Sym.zSwap_runWeight_add_runWeight`. So `HJO.Sym.isZDelta_mul_of_zSwap_eq`
pulls the invariant factor out and `HJO.Sym.isZDelta_runWeight` turns `a_m(l_1, 0)` into
`a_m(l_1, 1)`.

This is the per-class step of `HJO.Dyck.isZDelta_auxToFrac_unnormalisedCharSeries`. What it
does *not* do is sum over the classes, which is what that statement adds. -/
theorem isZDelta_auxToFrac_finsum_labelClass (q : K) {r : ℕ} (hx : IsPartialDyck (k + 1) N x)
    (hσ : Function.Injective σ) {a : Fin (k + 1)} (ha : σ a = k + r)
    (hb : ∀ b : Fin (k + 1), σ b = k + r + 1 → (a : ℕ) < (b : ℕ))
    (hw : w ∈ noAttackLabellings x σ) :
    IsZDelta q r
      (auxToFrac K (k + 1) (∑ᶠ v ∈ labelClass x σ (k + r) w,
        scalarSeries K (k + 1) q ^ invNumber (attackSet x) (wordOfFin v) * zmon K (k + 1) v))
      (auxToFrac K (k + 1) (∑ᶠ v ∈ labelClass x (transposeTuple (k + r) σ) (k + r)
          (transposeTuple (k + r) w),
        scalarSeries K (k + 1) q ^ invNumber (attackSet x) (wordOfFin v) * zmon K (k + 1) v)) := by
  have hτw : transposeTuple (k + r) w ∈ noAttackLabellings x (transposeTuple (k + r) σ) :=
    (bijOn_transposeTuple x σ (k + r)).mapsTo hw
  have hτa : transposeTuple (k + r) σ a = k + r + 1 := by
    simp only [transposeTuple, Function.comp_apply, ha, Equiv.swap_apply_left]
  rw [finsum_labelClass q hx hw (j₀ := a) (Or.inl ha),
    finsum_labelClass q hx hτw (j₀ := a) (Or.inr hτa)]
  simp only [labelSupport_transposeTuple, labelRun_transposeTuple, labelRunCount_transposeTuple]
  have hak : (a : ℕ) < N := lt_of_lt_of_le a.isLt hx.le_length
  have hs1 : sortNth (labelSupport (k + r) w) 1 = (a : ℕ) :=
    sortNth_one_eq_of_entry hx hw hσ ha hb
  have hwa : wordOfFin w (a : ℕ) = k + r := by
    rw [wordOfFin_eq_of_lt_level hx.le_length hw a.isLt]
    simpa using ha
  have hτwa : wordOfFin (transposeTuple (k + r) w) (a : ℕ) = k + r + 1 := by
    rw [wordOfFin_of_lt _ hak, transposeTuple_apply,
      show w ⟨(a : ℕ), hak⟩ = k + r from by rw [← wordOfFin_of_lt w hak]; exact hwa,
      Equiv.swap_apply_left]
  rw [show decide (wordOfFin w (sortNth (labelSupport (k + r) w) 1) = k + r + 1) = false from by
      rw [hs1, hwa]; simp,
    show decide (wordOfFin (transposeTuple (k + r) w) (sortNth (labelSupport (k + r) w) 1)
        = k + r + 1) = true from by rw [hs1, hτwa]; simp]
  have hg : ∏ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) ∉ labelSupport (k + r) w),
        zvar K (k + 1) (transposeTuple (k + r) w i)
      = ∏ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) ∉ labelSupport (k + r) w),
        zvar K (k + 1) (w i) :=
    Finset.prod_congr rfl fun i hi => by
      rw [transposeTuple_apply_of_notMem (k + r) w (mem_filter.1 hi).2]
  rw [card_filter_invSet_eq_of_labelSupport_eq (x := x) (m := k + r) (w := w)
      (w' := transposeTuple (k + r) w) (labelSupport_transposeTuple (k + r) w)
      (fun i hi => transposeTuple_apply_of_notMem (k + r) w hi), hg]
  have hp : 1 ≤ #(labelSupport (k + r) w) := one_le_card_labelSupport hx hw (Or.inl ha)
  have hCsub : labelCutSet x (k + r) w ⊆ Ico 1 #(labelSupport (k + r) w) := cutSet_subset_Ico _ _
  have hl1 : 1 ≤ #(labelRun x (k + r) w 1) :=
    one_le_card_cutBlock (cutBlock_nonempty hp hCsub le_rfl (by omega))
  refine isZDelta_auxToFrac_mul_mul _ _ _ _ _ ?_ ?_ ?_ ?_ ?_
  · rw [map_pow, auxToFrac_scalarSeries]
    exact pow_mem (C_scalarFrac_mem_zSwapFixedSubring q r) _
  · rw [map_prod]
    refine prod_mem fun i hi => ?_
    obtain ⟨h1, h2⟩ := ne_and_ne_of_notMem_twoLetterSupport i.isLt (mem_filter.1 hi).2
    rw [wordOfFin_val] at h1 h2
    exact ⟨auxToFrac_zvar_mem_zRing K k (w i), zSwap_auxToFrac_zvar_of_ne h1 h2⟩
  · rw [map_prod]
    refine prod_mem fun t _ => ?_
    rw [map_add, auxToFrac_runWeightZvar_level_add, auxToFrac_runWeightZvar_level_add]
    exact ⟨add_mem_zRing (runWeight_zLetter_mem_zRing q r _ false)
      (runWeight_zLetter_mem_zRing q r _ true), zSwap_runWeight_add_runWeight q r _⟩
  · rw [auxToFrac_runWeightZvar_level_add]
    exact runWeight_zLetter_mem_zRing q r _ false
  · rw [auxToFrac_runWeightZvar_level_add, auxToFrac_runWeightZvar_level_add]
    exact isZDelta_runWeight q r hl1

/-! ### The main statement -/

/-- The equation of `HJO.Sym.IsZDelta` at the zero series, which is what an empty key class
contributes. -/
private theorem isZDelta_zero (q : K) (r : ℕ) :
    IsZDelta q r (0 : AuxAlphabetSeriesFrac K (k + 1)) 0 := by
  rw [IsZDelta, zdeltaNum_apply, zSwap_apply, zPerm_zero]
  ring

/-- The per-key step: on each key class of merged degree `d`, `Δ_m` carries the class sum for `σ` to
the class sum for `τ_m σ`. Where the key class is empty both sides are `0`, and the relabelling
matches the empty key classes on the two sides. -/
private theorem isZDelta_auxToFrac_classPart (q : K) {r : ℕ} (hx : IsPartialDyck (k + 1) N x)
    (hσ : Function.Injective σ) {a : Fin (k + 1)} (ha : σ a = k + r)
    (hb : ∀ b : Fin (k + 1), σ b = k + r + 1 → (a : ℕ) < (b : ℕ)) (d : ℕ) (c : Fin N → ℕ) :
    IsZDelta q r (auxToFrac K (k + 1) (classPart q x σ (k + r) d c))
      (auxToFrac K (k + 1) (classPart q x (transposeTuple (k + r) σ) (k + r) d c)) := by
  have hkm : k ≤ k + r := Nat.le_add_right k r
  by_cases hne : (keyClass x σ (k + r) d c).Nonempty
  · obtain ⟨v, hv⟩ := hne
    rw [classPart, classPart, keyClass_eq_labelClass hkm hv,
      keyClass_eq_labelClass hkm (transposeTuple_mem_keyClass hkm hv)]
    exact isZDelta_auxToFrac_finsum_labelClass q hx hσ ha hb (mem_keyClass.1 hv).1
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have hne' : keyClass x (transposeTuple (k + r) σ) (k + r) d c = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      rintro ⟨v, hv⟩
      have h := transposeTuple_mem_keyClass hkm hv
      rw [transposeTuple_transposeTuple] at h
      rw [hne] at h
      exact h
    rw [classPart, classPart, hne, hne', finsum_mem_empty, map_zero]
    exact isZDelta_zero q r

/-- The main statement on the part of one merged degree: the classes of that degree are indexed by
their key, each contributes an `IsZDelta` pair by `HJO.Dyck.isZDelta_auxToFrac_classPart`, the
family is monomialwise finite, and `HJO.Sym.isZDelta_summableSum` sums it. -/
private theorem isZDelta_auxToFrac_unnormalisedCharPart (q : K) {r : ℕ}
    (hx : IsPartialDyck (k + 1) N x) (hσ : Function.Injective σ) {a : Fin (k + 1)}
    (ha : σ a = k + r) (hb : ∀ b : Fin (k + 1), σ b = k + r + 1 → (a : ℕ) < (b : ℕ)) (d : ℕ) :
    IsZDelta q r (auxToFrac K (k + 1) (unnormalisedCharPart q k x σ d))
      (auxToFrac K (k + 1) (unnormalisedCharPart q k x (transposeTuple (k + r) σ) d)) := by
  rw [auxToFrac_unnormalisedCharPart_eq q x σ (k + r) d,
    auxToFrac_unnormalisedCharPart_eq q x (transposeTuple (k + r) σ) (k + r) d]
  exact (isZDelta_summableSum (fun c => auxToFrac_classPart_mem_zGraded q x σ (k + r) d c)
    (isSummableFamily_zSeries (isSummableFamily_auxToFrac_classPart q x σ (k + r) d))
    fun c => isZDelta_auxToFrac_classPart q hx hσ ha hb d c).2.2

/-- **The swapping operators in the free variables**
`HJO.Dyck.isZDelta_auxToFrac_unnormalisedCharSeries`: for a partial Dyck path `π ∈ 𝔻_{k+1,N}`, a
prescription `σ` with pairwise distinct entries which has the entry `m = k + r` and which has the
entry `m + 1` — if at all — only later,

`χ'_{τ_m σ}(π) = Δ_m(χ'_σ(π))`,

stated as the equation of `HJO.Sym.IsZDelta` satisfied by the pair, which by
`HJO.Sym.eq_of_isZDelta` determines the right-hand side and is the form the whole `Δ_m` layer is
written in.

This is the case `HJO.Dyck.auxToFrac_unnormalisedCharSeries_transposeTuple` excludes: `m ≥ k`, so
`Δ_m` interchanges the last auxiliary variable with the first letter or two letters, and the
quotient is the one the merged grading supplies. Both series lie in `⨁_{d ≤ N}Z^{(k+1)}_d` by
`HJO.Dyck.auxToFrac_unnormalisedCharPart_mem_zGraded`, the decomposition being
`HJO.Dyck.unnormalisedCharPart`; within each merged degree the classes of
`HJO.Dyck.equivalence_labelClass` are indexed by `HJO.Dyck.labelClassKey`, which `τ_m` leaves alone,
so `HJO.Dyck.isZDelta_auxToFrac_finsum_labelClass` applies to each of them and
`HJO.Sym.isZDelta_summableSum` sums the monomialwise finite family. -/
@[hjo "lem_cm_swapping_free"]
theorem isZDelta_auxToFrac_unnormalisedCharSeries (q : K) {r : ℕ}
    (hx : IsPartialDyck (k + 1) N x) (hσ : Function.Injective σ)
    (ha : ∃ a : Fin (k + 1), σ a = k + r)
    (hlt : ∀ a b : Fin (k + 1), σ a = k + r → σ b = k + r + 1 → (a : ℕ) < (b : ℕ)) :
    IsZDelta q r (auxToFrac K (k + 1) (unnormalisedCharSeries q (k + 1) x σ))
      (auxToFrac K (k + 1) (unnormalisedCharSeries q (k + 1) x (transposeTuple (k + r) σ))) := by
  obtain ⟨a, ha⟩ := ha
  rw [← sum_auxToFrac_unnormalisedCharPart, ← sum_auxToFrac_unnormalisedCharPart]
  refine isZDelta_sum (fun d _ => zGraded_subset_zRing K k d
    (auxToFrac_unnormalisedCharPart_mem_zGraded q k x σ d)) fun d _ => ?_
  exact isZDelta_auxToFrac_unnormalisedCharPart q hx hσ ha (fun b hb => hlt a b ha hb) d

end HJO.Dyck
