/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.SuperWords
public import HJO.Classical.StdFibre
public meta import HJO.Attr

/-! # The super standardisation: its descent set, its fibres, and the signs of its inversions

Three things the expansion over the super alphabet asks of the super standardisation
`HJO.Sym.superStd` are proved here: that `Des(Std^±(v)) ⊆ T` is a blockwise-increase condition on
`v`, that the fibre of `Std^±` over a permutation `σ` sums to the super fundamental of `Des(σ⁻¹)`,
and that the super inversion number splits as the plain inversion number of the absolute values plus
the equal-partner counts at the negative positions.

## Main definitions

* `HJO.Sym.IsSuperAscendingWord`: the words the super fundamental `F̃_{n,S}` sums over.
* `HJO.Sym.superStdPerm`: `Std^±(v)` packaged as a permutation of the positions.

## Main results

* `HJO.Sym.descentSet_superStd_subset_iff`: blockwise increase is a descent condition on the super
  standardisation.
* `HJO.Sym.sum_superMonomial_superStdPerm`: a super standardisation fibre is a super fundamental,
  after truncation.
* `HJO.Dyck.superInvNumber_eq_invNumber_add_sum_equalPartners`: the super inversion number splits
  off the signs, `inv^±(R, v) = inv(R, |v|) + ∑_{i : v_i negative}d_i(R, |v|)`.

## Implementation notes

`HJO.Sym.stdPerm_eq_iff_of_injective` is the engine of the fibre lemma and is stated for an
arbitrary *injective* key: `Std(κ) = σ` holds exactly when `κ ∘ σ⁻¹` increases across every single
step. At an injective key no tie is ever broken, so the interval-constancy argument of
`HJO.Sym.isAscendingWord_comp_symm_iff` — the same statement for the plain standardisation, whose
words may repeat a letter — is not needed: the super tie-breaks are already inside
`HJO.Sym.superKey`, and the super fibre condition is that lemma at `κ = superKey v`.

*The fibre identity is stated after truncation, and its right-hand side is the truncated super
fundamental rather than the series.* `∑_{v}z_v` over a fibre is not a `Finset.sum`: infinitely many
super words standardise to a given `σ`. The convention for the plain statement
`HJO.ParkingFunctions.sum_wordMonomial_stdPerm` is to state the identity after `tr_m`, which turns
each side into the finite sum over the words whose letters are among the first `m`, the family of
those sums determining the element by `HJO.Sym.ext_letterTrunc`;
`HJO.ParkingFunctions.sum_wordMonomial_stdPerm` is that statement. The same convention is used here,
with the truncation taken over an arbitrary finite set `L` of letters, and with the right-hand side
written out as the sum over the super ascending words in `L` — which is exactly what `F̃_{n,S}` is
the sum of — because the series `F̃_{n,S}` itself, the series over the words of
`HJO.Sym.IsSuperAscendingWord`, is defined only later, as `HJO.Sym.superFundamental` in
`HJO.CarlssonMellit.SuperSchur`. The series form follows from
`HJO.Sym.sum_superMonomial_superStdPerm` by summing over `L`.

`IsSuperAscendingWord` carries the three defining clauses as its three fields; the equivalent
single-step disjunction `HJO.Sym.isSuperAscendingWord_iff` is what the proofs use, the sign of a
letter being positive exactly when it is not negative.

`HJO.Dyck.superInvNumber_eq_invNumber_add_sum_equalPartners` is usually stated for an `R` of
increasing pairs. That hypothesis is not
used — neither the splitting of the inversion set nor the fiberwise count of the equal pairs looks
at the order of a pair — so it is dropped.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc.
**31** (2018) 661--697, Section 3.
-/

@[expose] public section

open Finset

namespace HJO.Sym

variable {n : ℕ}

/-! ### The standardisation of an injective key -/

section Key

variable {α : Type*} [LinearOrder α]

/-- **At an injective key the standardisation compares the letters outright**: no tie is ever
broken, so `Std(κ)_i < Std(κ)_j` is `κ_i < κ_j`. -/
theorem std_lt_std_iff_of_injective {κ : Fin n → α} (hκ : Function.Injective κ) (i j : Fin n) :
    std κ i < std κ j ↔ κ i < κ j := by
  rw [std_lt_std_iff]
  exact ⟨fun h => h.elim id fun h' => absurd (hκ h'.1) (Fin.ne_of_lt h'.2), Or.inl⟩

/-- **The fibre condition at an injective key**: `Std(κ) = σ` holds exactly when the key increases
across every single step of the listing `σ` prescribes, that is when `κ ∘ σ⁻¹` is strictly
increasing.

Forwards is `HJO.Sym.std_lt_std_iff` at the two positions `σ⁻¹(r)`, `σ⁻¹(r+1)`, whose
standardisations are consecutive; backwards the strict steps make `κ ∘ σ⁻¹` strictly monotone, so
the comparisons of `σ` are the comparisons of `κ`, which by `std_lt_std_iff_of_injective` are the
comparisons of `Std(κ)`, and `HJO.Sym.eq_of_lt_iff_lt` finishes. -/
theorem stdPerm_eq_iff_of_injective {κ : Fin n → α} (hκ : Function.Injective κ)
    (σ : Equiv.Perm (Fin n)) :
    stdPerm κ = σ ↔ ∀ r r' : Fin n, (r : ℕ) + 1 = (r' : ℕ) → κ (σ.symm r) < κ (σ.symm r') := by
  constructor
  · intro hst r r' hrr'
    have hval : ∀ k : Fin n, std κ (σ.symm k) = (k : ℕ) := fun k => by
      rw [← stdPerm_apply, hst, Equiv.apply_symm_apply]
    have hlt : std κ (σ.symm r) < std κ (σ.symm r') := by rw [hval, hval]; omega
    exact (std_lt_std_iff_of_injective hκ _ _).1 hlt
  · intro hstep
    have hmono : StrictMono fun r => κ (σ.symm r) := by
      cases n with
      | zero => exact fun a => a.elim0
      | succ N => exact Fin.strictMono_iff_lt_succ.2 fun i => hstep _ _ (by simp)
    have hkey : ∀ i j : Fin n, κ i < κ j ↔ σ i < σ j := fun i j => by
      have hi : κ i = (fun r => κ (σ.symm r)) (σ i) := by simp
      have hj : κ j = (fun r => κ (σ.symm r)) (σ j) := by simp
      rw [hi, hj, hmono.lt_iff_lt]
    have := eq_of_lt_iff_lt (π := fun i => (stdPerm κ i : Fin n)) (σ := fun i => (σ i : Fin n))
      (stdPerm κ).bijective σ.bijective fun i j => by
        rw [Fin.lt_def, stdPerm_apply, stdPerm_apply, std_lt_std_iff_of_injective hκ, hkey]
    exact Equiv.ext fun i => congrFun this i

end Key

/-! ### The super standardisation across a step -/

section Step

/-- **The super standardisation across a pair of positions in order**: for `i < j` the rank of `i`
is the smaller exactly when its letter precedes that of `j`, or the two letters are equal and
positive.

The four cases of the proof: the two strict comparisons of the letters are settled by
`HJO.Sym.superStd_lt_superStd_of_lt`, and at equal letters the two tie-breaking rules decide, in
opposite directions. -/
theorem superStd_lt_superStd_iff_of_lt {v : Fin n → SuperLetter} {i j : Fin n} (hij : i < j) :
    superStd v i < superStd v j ↔ v i < v j ∨ (v i = v j ∧ (v i).IsPositive) := by
  have hij' : (i : ℕ) < (j : ℕ) := hij
  rcases lt_trichotomy (v i) (v j) with h | h | h
  · exact iff_of_true (superStd_lt_superStd_of_lt h) (Or.inl h)
  · by_cases hneg : (v i).IsNegative
    · rw [superStd_lt_superStd_iff_of_isNegative h hneg]
      refine iff_of_false (by omega) fun hc => ?_
      exact hc.elim (fun hc' => absurd h (ne_of_lt hc'))
        fun hc' => absurd hc'.2 ((SuperLetter.isPositive_iff_not_isNegative _).1 · hneg)
    · have hpos : (v i).IsPositive := (SuperLetter.isPositive_iff_not_isNegative _).2 hneg
      rw [superStd_lt_superStd_iff_of_isPositive h hpos]
      exact iff_of_true hij' (Or.inr ⟨h, hpos⟩)
  · refine iff_of_false (asymm (superStd_lt_superStd_of_lt h)) fun hc => ?_
    exact hc.elim (fun hc' => absurd hc' (asymm h)) fun hc' => absurd hc'.1 (ne_of_gt h)

/-- **Blockwise increase is a descent condition on the super
standardisation.** `Des(Std^±(v)) ⊆ T` holds exactly when, across every step outside `T`, either the
letter of `v` increases strictly or the two letters are equal and positive.

The entries of `Std^±(v)` at two adjacent positions are distinct, so a step is a non-descent exactly
when it is an ascent, and `HJO.Sym.superStd_lt_superStd_iff_of_lt` reads that off the letters: the
two cases in which the earlier rank is the smaller are the two the statement allows. -/
@[hjo "lem_om_super_block_std"]
theorem descentSet_superStd_subset_iff (T : Finset ℕ) (v : Fin n → SuperLetter) :
    descentSet n (finWord (superStd v)) ⊆ T ↔
      ∀ k l : Fin n, (k : ℕ) + 1 = (l : ℕ) → (l : ℕ) ∉ T →
        v k < v l ∨ (v k = v l ∧ (v k).IsPositive) := by
  constructor
  · intro hsub k l hkl hl
    by_contra hc
    have hkl' : k < l := Fin.lt_def.2 (by omega)
    refine hl (hsub (mem_descentSet.2 ⟨by omega, l.isLt, ?_⟩))
    rw [finWord_of_lt _ l.isLt, finWord_of_lt _ (by omega : (l : ℕ) - 1 < n),
      show (⟨(l : ℕ), l.isLt⟩ : Fin n) = l from rfl,
      show (⟨(l : ℕ) - 1, by omega⟩ : Fin n) = k from
        Fin.ext (show (l : ℕ) - 1 = (k : ℕ) by omega)]
    have hnot : ¬ superStd v k < superStd v l := fun hlt =>
      hc ((superStd_lt_superStd_iff_of_lt hkl').1 hlt)
    have hne : superStd v k ≠ superStd v l := fun h =>
      absurd (superStd_injective v h) (Fin.ne_of_lt hkl')
    omega
  · intro hstep j hj
    obtain ⟨h1, h2, h3⟩ := mem_descentSet.1 hj
    by_contra hjT
    have hk : j - 1 < n := by omega
    rw [finWord_of_lt _ h2, finWord_of_lt _ hk] at h3
    have hkl : ((⟨j - 1, hk⟩ : Fin n) : ℕ) + 1 = ((⟨j, h2⟩ : Fin n) : ℕ) := by simp; omega
    have hlt : (⟨j - 1, hk⟩ : Fin n) < ⟨j, h2⟩ := Fin.lt_def.2 (by simp; omega)
    exact absurd ((superStd_lt_superStd_iff_of_lt hlt).2 (hstep _ _ hkl hjT)) (asymm h3)

end Step

/-! ### The words the super fundamental sums over -/

section Ascending

/-- A letter that is not positive is negative: the sign takes two values. -/
private theorem isNegative_of_not_isPositive {α : SuperLetter} (h : ¬α.IsPositive) :
    α.IsNegative :=
  not_not.1 fun hn => h ((SuperLetter.isPositive_iff_not_isNegative α).2 hn)

/-- **The super ascending words for a step set `S`**: the words `v ∈ 𝒜^n` the super
fundamental `F̃_{n,S}` sums the monomials `z_v` of. Weakly increasing for the order of the super
alphabet, with a repetition of a *positive* letter forbidden at a step of `S` and a repetition of a
*negative* letter required to be at one — the three clauses of
the definition of `F̃_{n,S}`, which are the conditions the two opposite tie-breaks of
`HJO.Sym.superStd` produce.

Steps are indexed by the later of the two positions they join, matching `HJO.Sym.IsAscendingWord`
and `HJO.Sym.descentSet`: the step `j` of `F̃_{n,S}`, between the `1`-based positions `j` and
`j + 1`, is the step into the `0`-based position `l = j`. -/
@[hjo "def_cm_super_fundamental"]
structure IsSuperAscendingWord (n : ℕ) (S : Finset ℕ) (v : Fin n → SuperLetter) : Prop where
  /-- A super ascending word does not decrease at any step. -/
  le_of_step : ∀ k l : Fin n, (k : ℕ) + 1 = (l : ℕ) → v k ≤ v l
  /-- A repetition of a positive letter is not at a step of `S`. -/
  notMem_of_isPositive : ∀ k l : Fin n, (k : ℕ) + 1 = (l : ℕ) → v k = v l → (v k).IsPositive →
    (l : ℕ) ∉ S
  /-- A repetition of a negative letter is at a step of `S`. -/
  mem_of_isNegative : ∀ k l : Fin n, (k : ℕ) + 1 = (l : ℕ) → v k = v l → (v k).IsNegative →
    (l : ℕ) ∈ S

/-- The three clauses of a super ascending word, read at one step at a time: the letter increases
strictly, or it repeats and its sign decides whether the step belongs to `S`. This is the form the
proofs use, the two sign clauses being opposite. -/
theorem isSuperAscendingWord_iff (S : Finset ℕ) (v : Fin n → SuperLetter) :
    IsSuperAscendingWord n S v ↔ ∀ k l : Fin n, (k : ℕ) + 1 = (l : ℕ) →
      v k < v l ∨ (v k = v l ∧ ((v k).IsPositive ↔ (l : ℕ) ∉ S)) := by
  constructor
  · intro h k l hkl
    rcases lt_or_eq_of_le (h.le_of_step k l hkl) with hlt | heq
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, h.notMem_of_isPositive k l hkl heq, fun hnot => ?_⟩
      by_contra hpos
      exact hnot (h.mem_of_isNegative k l hkl heq (isNegative_of_not_isPositive hpos))
  · intro h
    refine ⟨fun k l hkl => ?_, fun k l hkl heq hpos => ?_, fun k l hkl heq hneg => ?_⟩
    · exact (h k l hkl).elim le_of_lt fun h' => le_of_eq h'.1
    · exact ((h k l hkl).resolve_left (by rw [heq]; exact lt_irrefl _)).2.1 hpos
    · by_contra hmem
      exact absurd (((h k l hkl).resolve_left (by rw [heq]; exact lt_irrefl _)).2.2 hmem)
        ((SuperLetter.isPositive_iff_not_isNegative _).1 · hneg)

instance instDecidableIsSuperAscendingWord (n : ℕ) (S : Finset ℕ) (v : Fin n → SuperLetter) :
    Decidable (IsSuperAscendingWord n S v) :=
  decidable_of_iff _ (isSuperAscendingWord_iff S v).symm

end Ascending

/-! ### The fibres of the super standardisation -/

section Fibre

/-- **The key of the super standardisation is injective**: it carries the letter together with a
tie-break that separates two positions of one letter, in the direction the letter's sign
prescribes. This is what makes the fibre condition a strict-increase condition, no tie being left
for `HJO.Sym.std` to break. -/
theorem superKey_injective (v : Fin n → SuperLetter) : Function.Injective (superKey v) := by
  intro i j h
  have hi := i.isLt
  have hj := j.isLt
  have h1 : v i = v j := congrArg (fun p => (ofLex p).1) h
  have h2 : superTie n (v i) (i : ℕ) = superTie n (v j) (j : ℕ) :=
    congrArg (fun p => (ofLex p).2) h
  by_cases hneg : (v i).IsNegative
  · rw [superTie_of_isNegative hneg, superTie_of_isNegative (h1 ▸ hneg)] at h2
    exact Fin.ext (by omega)
  · have hpos : (v i).IsPositive := (SuperLetter.isPositive_iff_not_isNegative _).2 hneg
    rw [superTie_of_isPositive hpos, superTie_of_isPositive (h1 ▸ hpos)] at h2
    exact Fin.ext h2

/-- `Std^±(v)` packaged as a permutation of the positions: the standardisation of the key
`HJO.Sym.superKey`, which is what `HJO.Sym.superStd` is. -/
noncomputable def superStdPerm (v : Fin n → SuperLetter) : Equiv.Perm (Fin n) :=
  stdPerm (superKey v)

@[simp]
theorem superStdPerm_apply (v : Fin n → SuperLetter) (i : Fin n) :
    ((superStdPerm v i : Fin n) : ℕ) = superStd v i := rfl

/-- **The fibre condition of the super standardisation.** `Std^±(v) = σ` holds exactly when the word
`r ↦ v_{σ⁻¹(r)}`, which lists the letters of `v` in the order `σ` ranks them, is a super ascending
word for `Des(σ⁻¹)`.

The key `HJO.Sym.superKey` is injective, so by `HJO.Sym.stdPerm_eq_iff_of_injective` the condition
is that the key increases across every step of the listing. At a step the letters decide unless
they are equal, and then the tie-break does: a positive letter compares the two positions in
increasing order, so the step is a non-descent of `σ⁻¹`, and a negative one in decreasing order, so
it is a descent — which are the two sign clauses of `HJO.Sym.IsSuperAscendingWord`. -/
theorem superStdPerm_eq_iff (σ : Equiv.Perm (Fin n)) (v : Fin n → SuperLetter) :
    superStdPerm v = σ ↔ IsSuperAscendingWord n (invDescentSet σ) (v ∘ σ.symm) := by
  rw [superStdPerm, stdPerm_eq_iff_of_injective (superKey_injective v) σ, isSuperAscendingWord_iff]
  refine forall_congr' fun r => forall_congr' fun r' => imp_congr_right fun hrr' => ?_
  rw [superKey_lt_superKey_iff]
  refine or_congr Iff.rfl (and_congr_right fun heq => ?_)
  have hmem := mem_invDescentSet_iff σ (show 1 ≤ (r' : ℕ) by omega) r'.isLt
  rw [show (⟨(r' : ℕ), r'.isLt⟩ : Fin n) = r' from rfl,
    show (⟨(r' : ℕ) - 1, by omega⟩ : Fin n) = r from
      Fin.ext (show (r' : ℕ) - 1 = (r : ℕ) by omega)] at hmem
  have hmem' : (r' : ℕ) ∈ invDescentSet σ ↔ ((σ.symm r' : Fin n) : ℕ) < ((σ.symm r : Fin n) : ℕ) :=
    hmem.trans Fin.lt_def
  have hne : ((σ.symm r : Fin n) : ℕ) ≠ ((σ.symm r' : Fin n) : ℕ) := fun hc =>
    absurd (σ.symm.injective (Fin.ext hc)) (Fin.ne_of_val_ne (show (r : ℕ) ≠ (r' : ℕ) by omega))
  rw [← heq, superTie_lt_superTie_iff, hmem']
  by_cases hpos : (v (σ.symm r)).IsPositive
  · have hnn : ¬(v (σ.symm r)).IsNegative := (SuperLetter.isPositive_iff_not_isNegative _).1 hpos
    simp only [Function.comp_apply, hpos, hnn, true_and, false_and, or_false, true_iff]
    omega
  · have hn : (v (σ.symm r)).IsNegative := isNegative_of_not_isPositive hpos
    simp only [Function.comp_apply, hpos, hn, false_and, true_and, false_or, false_iff, not_not]

/-- Reindexing a super word by a permutation of the positions leaves its monomial unchanged: the two
products have the same factors in a different order. -/
theorem superMonomial_comp (K : Type*) [CommRing K] (q : K) (e : Equiv.Perm (Fin n))
    (v : Fin n → SuperLetter) : superMonomial K q (v ∘ e) = superMonomial K q v :=
  Fintype.prod_equiv e _ _ fun _ => rfl

/-- **A super standardisation fibre is a super fundamental.**
`∑_{v : Std^±(v) = σ}z_v = F̃_{n,Des(σ⁻¹)}`, stated after truncation to a finite set `L` of letters:
the sum of `z_v` over the super words with letters in `L` that standardise to `σ` is the sum of
`z_v` over the super words with letters in `L` that are super ascending for `Des(σ⁻¹)`, which are
the words `F̃_{n,Des(σ⁻¹)}` sums over. Taking `L` to be the letters of absolute value below `m` is
the truncation `tr_m`, and the family of those identities determines the series identity, exactly
as for the plain statement `HJO.ParkingFunctions.sum_wordMonomial_stdPerm`.

The bijection is `v ↦ v ∘ σ⁻¹`, which lists the letters of `v` in the order `σ` ranks them: it
preserves the monomial and, by `HJO.Sym.superStdPerm_eq_iff`, carries the fibre onto the super
ascending words. -/
@[hjo "lem_cm_super_std_fibre"]
theorem sum_superMonomial_superStdPerm (K : Type*) [CommRing K] (q : K) (σ : Equiv.Perm (Fin n))
    (L : Finset SuperLetter) :
    ∑ v ∈ {v ∈ Fintype.piFinset fun _ : Fin n => L | superStdPerm v = σ}, superMonomial K q v
      = ∑ v ∈ {v ∈ Fintype.piFinset fun _ : Fin n => L |
          IsSuperAscendingWord n (invDescentSet σ) v}, superMonomial K q v := by
  refine Finset.sum_nbij' (fun v => v ∘ σ.symm) (fun a => a ∘ σ) (fun v hv => ?_) (fun a ha => ?_)
    (fun v _ => ?_) (fun a _ => ?_) fun v hv => ?_
  · rw [mem_filter, Fintype.mem_piFinset] at hv ⊢
    exact ⟨fun k => hv.1 _, (superStdPerm_eq_iff σ v).1 hv.2⟩
  · rw [mem_filter, Fintype.mem_piFinset] at ha ⊢
    refine ⟨fun k => ha.1 _, (superStdPerm_eq_iff σ (a ∘ σ)).2 ?_⟩
    have h : (a ∘ σ) ∘ σ.symm = a := funext fun k => by simp
    rw [h]
    exact ha.2
  · exact funext fun i => by simp
  · exact funext fun k => by simp
  · exact (superMonomial_comp K q σ.symm v).symm

end Fibre

end HJO.Sym

namespace HJO.Dyck

open HJO.Sym

/-! ### The super inversion number splits off the signs -/

variable {n : ℕ}

/-- **The super inversions split into the plain inversions of the absolute values and the equal
pairs led by a negative letter.** At a pair whose two absolute values differ, the letters are
compared by their absolute values alone and no repetition can occur; at a pair whose absolute values
agree, the pair is a super inversion exactly when its earlier letter is negative, whichever sign the
later one carries. -/
theorem superInvSet_eq_invSet_superAbs_union (R : Finset (Fin n × Fin n))
    (v : Fin n → SuperLetter) :
    superInvSet R v = invSet R (superAbs v)
      ∪ {p ∈ R | superAbs v p.1 = superAbs v p.2 ∧ (v p.1).IsNegative} := by
  rw [superInvSet, invSet, ← Finset.filter_or]
  refine Finset.filter_congr fun p _ => ?_
  simp only [superAbs_apply]
  constructor
  · rintro (h | ⟨heq, hneg⟩)
    · rcases SuperLetter.lt_iff.1 h with h' | ⟨h', _, hneg⟩
      · exact Or.inl h'
      · exact Or.inr ⟨h'.symm, hneg⟩
    · exact Or.inr ⟨congrArg SuperLetter.absVal heq, hneg⟩
  · rintro (h | ⟨heq, hneg⟩)
    · exact Or.inl (SuperLetter.lt_of_absVal_lt h)
    · by_cases hneg2 : (v p.2).IsNegative
      · exact Or.inr ⟨SuperLetter.ext heq (hneg.trans hneg2.symm), hneg⟩
      · exact Or.inl (SuperLetter.lt_iff.2
          (Or.inr ⟨heq.symm, (SuperLetter.isPositive_iff_not_isNegative _).2 hneg2, hneg⟩))

/-- **The super inversion number splits off the signs.**
`inv^±(R, v) = inv(R, |v|) + ∑_{i : v_i negative}d_i(R, |v|)`.

The pairs of `R` whose two absolute values differ contribute exactly the inversions of `|v|`, and
those whose absolute values agree contribute exactly the pairs led by a negative letter, which
grouped by their first position are the equal-partner counts at the negative positions. The
hypothesis that the pairs of `R` increase is not needed. -/
@[hjo "lem_cm_super_inv_split"]
theorem superInvNumber_eq_invNumber_add_sum_equalPartners (R : Finset (Fin n × Fin n))
    (v : Fin n → SuperLetter) :
    superInvNumber R v
      = invNumber R (superAbs v)
        + ∑ i ∈ {i | (v i).IsNegative}, equalPartners R (superAbs v) i := by
  have hdisj : Disjoint (invSet R (superAbs v))
      ({p ∈ R | superAbs v p.1 = superAbs v p.2 ∧ (v p.1).IsNegative} : Finset (Fin n × Fin n)) :=
    disjoint_filter_filter' _ _ (by
      refine Set.disjoint_left.2 fun p hp hp' => ?_
      exact absurd hp'.1 (ne_of_gt hp))
  rw [superInvNumber, superInvSet_eq_invSet_superAbs_union, card_union_of_disjoint hdisj,
    invNumber]
  congr 1
  refine (card_eq_sum_card_fiberwise (f := Prod.fst) fun p hp => ?_).trans
    (Finset.sum_congr rfl fun i hi => ?_)
  · simp only [mem_coe, mem_filter, mem_univ, true_and] at hp ⊢
    exact hp.2.2
  · simp only [mem_filter, mem_univ, true_and] at hi
    rw [Finset.filter_filter, equalPartners]
    refine congrArg Finset.card (Finset.ext fun p => ?_)
    simp only [mem_filter]
    constructor
    · rintro ⟨hpR, ⟨heq, -⟩, rfl⟩
      exact ⟨hpR, rfl, heq.symm⟩
    · rintro ⟨hpR, rfl, heq⟩
      exact ⟨hpR, ⟨heq.symm, hi⟩, rfl⟩

end HJO.Dyck
