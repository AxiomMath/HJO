/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Classical.CoStandardisation
public import HJO.Classical.GesselTruncation
public import HJO.DyckWordMonomial
public meta import HJO.Attr

/-! # A standardisation fibre is a fundamental

The fibre of the standardisation over a permutation `σ` is, monomial by monomial, the fundamental
quasisymmetric function of the inverse descent set of `σ`; and the fibre of the co-standardisation
is the fundamental of the complemented inverse descent set. Both are one bijection: reading a word
in the order `σ` prescribes turns the fibre condition into an ascending-word condition.

## Main definitions

* `HJO.Sym.coStdPerm`: `Std⁻(w)` packaged as a permutation of the positions.

## Main statements

* `HJO.Sym.std_lt_std_of_apply_lt_apply`.
* `HJO.Sym.isAscendingWord_comp_symm_iff`: the fibre condition *is* the ascending-word condition.
* `HJO.ParkingFunctions.sum_wordMonomial_stdPerm`.
* `HJO.ParkingFunctions.sum_wordMonomial_coStdPerm`.

## Implementation notes

*The sums are infinite and its two identities are stated after truncation.* `∑_{w}x_w`
over the whole fibre is not an element of `𝒫` formed by any `Finset.sum`; what `tr_m` does to it
is the finite sum over the words with letters among the first `m`, and the family of those sums over
all `m` determines the element, by `HJO.Sym.ext_letterTrunc`. So each identity is stated as: for
every
`m`, the finite sum over the fibre's words in the first `m` letters is `tr_m(F_{n,S})`. That is the
same convention `HJO.Dyck.markedCharSeries` records for `HJO.Dyck.charSeries`.
`HJO.ParkingFunctions.coeff_gessel_invDescentSet_eq_one` and its companion are the coefficientwise
reading, for a consumer that wants one monomial at a time.

The co-standardisation fibre is read off the standardisation fibre at the permutation
`τ = σ ∘ rev` (`HJO.Sym.invDescentSet_revPerm_trans` identifies `Des(τ⁻¹)` with the complement, with
*no* reversal — unlike `HJO.Sym.invDescentSet_trans_revPerm`, which reverses the *values* of `σ` and
therefore complements *and* reflects), together with `HJO.Sym.coStd_eq_std_wordReverse` and the
invariance of a monomial under reversing its word.

`HJO.Sym.wordExponent_comp_equiv` is `HJO.Sym.wordExponent_comp_bijective` of
`HJO.Shuffle.SweepStandardisation` stated for an `Equiv`; this file cannot import the sweep
tree, which sits far above it.

## References

This file proves `HJO.Sym.std_lt_std_of_apply_lt_apply`,
`HJO.ParkingFunctions.sum_wordMonomial_stdPerm` and
`HJO.ParkingFunctions.sum_wordMonomial_coStdPerm`.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### Increase across every step of an interval -/

/-- **A function increasing across each single step of an interval increases across it.** This is
transitivity run along the steps, and it is what turns "no descent of `σ⁻¹` between `r` and `s`"
into `σ⁻¹(r) < σ⁻¹(s)`. -/
theorem lt_of_forall_step {n : ℕ} {β : Type*} [Preorder β] {f : Fin n → β} {r s : Fin n}
    (hstep : ∀ l l' : Fin n, r ≤ l → (l : ℕ) + 1 = (l' : ℕ) → l' ≤ s → f l < f l')
    (hrs : r < s) : f r < f s := by
  have key : ∀ d : ℕ, ∀ t : Fin n, (t : ℕ) = (r : ℕ) + d + 1 → t ≤ s → f r < f t := by
    intro d
    induction d with
    | zero => exact fun t ht hts => hstep r t le_rfl (by omega) hts
    | succ d ih =>
      intro t ht hts
      have hts' : (t : ℕ) ≤ (s : ℕ) := hts
      have htn : (t : ℕ) < n := t.isLt
      have hm : (r : ℕ) + d + 1 < n := by omega
      have huval : ((⟨(r : ℕ) + d + 1, hm⟩ : Fin n) : ℕ) = (r : ℕ) + d + 1 := rfl
      have h1 : f r < f ⟨(r : ℕ) + d + 1, hm⟩ :=
        ih ⟨(r : ℕ) + d + 1, hm⟩ huval (Fin.le_def.2 (by omega))
      exact h1.trans (hstep ⟨(r : ℕ) + d + 1, hm⟩ t (Fin.le_def.2 (by omega)) (by omega) hts)
  have hrs' : (r : ℕ) < (s : ℕ) := hrs
  exact key ((s : ℕ) - (r : ℕ) - 1) s (by omega) le_rfl

/-! ### An ascending word transports the order -/

section Transport

variable {n : ℕ}

/-- The exponent vector does not see the order of the letters: reindexing a word by a bijection of
the positions leaves it unchanged. This is `HJO.Sym.wordExponent_comp_bijective` of the sweep tree,
stated for an `Equiv`. -/
theorem wordExponent_comp_equiv (e : Fin n ≃ Fin n) (w : Fin n → ℕ) :
    wordExponent (w ∘ e) = wordExponent w :=
  Fintype.sum_equiv e _ _ fun _ => rfl

/-- `Std(w) = σ` read entry by entry. -/
theorem stdPerm_eq_iff {α : Type*} [LinearOrder α] {w : Fin n → α} {σ : Equiv.Perm (Fin n)} :
    stdPerm w = σ ↔ ∀ i, std w i = ((σ i : Fin n) : ℕ) :=
  ⟨fun h i => by rw [← h, stdPerm_apply], fun h => Equiv.ext fun i => Fin.ext (by
    rw [stdPerm_apply, h i])⟩

/-- **An ascending word transports the order.** If `a` is an ascending word
for `Des(σ⁻¹)` and `w_i = a_{σ_i}`, then `σ_i < σ_j` forces `Std(w)_i < Std(w)_j`.

If `a_{σ_i} < a_{σ_j}` this is `HJO.Sym.std_lt_std_iff` outright. If the two letters are equal then
`a` is constant on the whole interval between them, so no step of that interval is a descent of
`σ⁻¹`, whence `σ⁻¹` increases across it and `i < j`; `HJO.Sym.std_lt_std_iff` then applies through
its tie-breaking clause. -/
@[hjo "lem_cm_std_transport"]
theorem std_lt_std_of_apply_lt_apply (σ : Equiv.Perm (Fin n)) {a : Fin n → ℕ}
    (ha : IsAscendingWord n (invDescentSet σ) a) {i j : Fin n} (hij : σ i < σ j) :
    std (a ∘ σ) i < std (a ∘ σ) j := by
  have hle : a (σ i) ≤ a (σ j) := ha.monotone hij.le
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact (std_lt_std_iff (a ∘ σ) i j).2 (Or.inl hlt)
  · have hconst : ∀ l : Fin n, σ i ≤ l → l ≤ σ j → a l = a (σ i) := fun l h1 h2 =>
      le_antisymm (heq ▸ ha.monotone h2) (ha.monotone h1)
    have hstep : ∀ l l' : Fin n, σ i ≤ l → (l : ℕ) + 1 = (l' : ℕ) → l' ≤ σ j →
        σ.symm l < σ.symm l' := by
      intro l l' h1 h2 h3
      have hll' : l < l' := Fin.lt_def.2 (by omega)
      have hlj : l ≤ σ j := hll'.le.trans h3
      have hl'i : σ i ≤ l' := h1.trans hll'.le
      have hnotD : (l' : ℕ) ∉ invDescentSet σ := by
        intro hmem
        have hlt' := ha.lt_of_mem l l' h2 hmem
        rw [hconst l h1 hlj, hconst l' hl'i h3] at hlt'
        exact absurd hlt' (lt_irrefl _)
      have h1' : 1 ≤ (l' : ℕ) := by omega
      have hiff := mem_invDescentSet_iff σ h1' l'.isLt
      have hl'val : (⟨(l' : ℕ), l'.isLt⟩ : Fin n) = l' := rfl
      have hlval : (⟨(l' : ℕ) - 1, by omega⟩ : Fin n) = l :=
        Fin.ext (show (l' : ℕ) - 1 = (l : ℕ) by omega)
      rw [hl'val, hlval] at hiff
      have hnot : ¬ (σ.symm l' < σ.symm l) := fun hc => hnotD (hiff.2 hc)
      have hne : (σ.symm l : Fin n) ≠ σ.symm l' := fun hc =>
        absurd (σ.symm.injective hc) (Fin.ne_of_val_ne (by omega))
      exact lt_of_le_of_ne (not_lt.1 hnot) hne
    have hsymm := lt_of_forall_step hstep hij
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hsymm
    exact (std_lt_std_iff (a ∘ σ) i j).2 (Or.inr ⟨heq, hsymm⟩)

/-- **The fibre condition is the ascending-word condition.** `Std(w) = σ` holds exactly when the
word `r ↦ w_{σ⁻¹(r)}`, which lists the letters of `w` in the order `σ` ranks them, is an ascending
word for `Des(σ⁻¹)`.

Forwards is `HJO.Sym.std_lt_std_iff` read at the two positions `σ⁻¹(r-1)`, `σ⁻¹(r)`: their
standardisations are consecutive, so the letters increase weakly, and strictly exactly when the step
is a descent of `σ⁻¹`. Backwards is `HJO.Sym.std_lt_std_of_apply_lt_apply` at both orders of the
pair, which gives the comparisons of `σ`, followed by `HJO.Sym.eq_of_lt_iff_lt`. -/
theorem isAscendingWord_comp_symm_iff (σ : Equiv.Perm (Fin n)) (w : Fin n → ℕ) :
    IsAscendingWord n (invDescentSet σ) (w ∘ σ.symm) ↔ stdPerm w = σ := by
  constructor
  · intro ha
    have hcomp : (w ∘ σ.symm) ∘ σ = w := funext fun i => by simp
    have hkey : ∀ i j : Fin n, (stdPerm w i : Fin n) < stdPerm w j ↔ σ i < σ j := by
      intro i j
      rw [Fin.lt_def, stdPerm_apply, stdPerm_apply]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · by_contra hc
        rcases lt_or_eq_of_le (not_lt.1 hc) with hc' | hc'
        · have := std_lt_std_of_apply_lt_apply σ ha hc'
          rw [hcomp] at this
          omega
        · rw [σ.injective hc'.symm] at h
          omega
      · have := std_lt_std_of_apply_lt_apply σ ha h
        rwa [hcomp] at this
    have := eq_of_lt_iff_lt (π := fun i => (stdPerm w i : Fin n)) (σ := fun i => (σ i : Fin n))
      (stdPerm w).bijective σ.bijective hkey
    exact Equiv.ext fun i => congrFun this i
  · intro hσ
    rw [stdPerm_eq_iff] at hσ
    have hval : ∀ k : Fin n, std w (σ.symm k) = (k : ℕ) := fun k => by
      rw [hσ (σ.symm k), Equiv.apply_symm_apply]
    refine ⟨monotone_of_le_succ fun k l hkl => ?_, fun k l hkl hmem => ?_⟩
    · have hlt : std w (σ.symm k) < std w (σ.symm l) := by rw [hval, hval]; omega
      rcases (std_lt_std_iff w (σ.symm k) (σ.symm l)).1 hlt with h | ⟨h, -⟩
      · exact le_of_lt h
      · exact le_of_eq h
    · have hlt : std w (σ.symm k) < std w (σ.symm l) := by rw [hval, hval]; omega
      have h1 : 1 ≤ (l : ℕ) := by omega
      have hiff := mem_invDescentSet_iff σ h1 l.isLt
      have hl'val : (⟨(l : ℕ), l.isLt⟩ : Fin n) = l := rfl
      have hlval : (⟨(l : ℕ) - 1, by omega⟩ : Fin n) = k :=
        Fin.ext (show (l : ℕ) - 1 = (k : ℕ) by omega)
      rw [hl'val, hlval] at hiff
      have hji : (σ.symm l : Fin n) < σ.symm k := hiff.1 hmem
      rcases (std_lt_std_iff w (σ.symm k) (σ.symm l)).1 hlt with h | ⟨-, h⟩
      · exact h
      · exact absurd h (asymm hji)

end Transport

/-! ### The co-standardisation as a permutation -/

section CoStdPerm

variable {α : Type*} [LinearOrder α] {n : ℕ}

/-- `Std⁻(w)` packaged as a permutation of the positions. -/
noncomputable def coStdPerm (w : Fin n → α) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective _ (coStd_bijective w)

@[simp]
theorem coStdPerm_apply (w : Fin n → α) (i : Fin n) :
    ((coStdPerm w i : Fin n) : ℕ) = coStd w i := rfl

/-- **The co-standardisation fibre is a standardisation fibre.** `Std⁻(w) = σ` holds exactly when
`Std(w^R) = σ ∘ rev`: `HJO.Sym.coStd_eq_std_wordReverse` says the two statistics agree after the
mirror, so the two fibre conditions are the same condition on the reversed word. -/
theorem coStdPerm_eq_iff_stdPerm_wordReverse {w : Fin n → α} {σ : Equiv.Perm (Fin n)} :
    coStdPerm w = σ ↔ stdPerm (wordReverse w) = Fin.revPerm.trans σ := by
  constructor
  · intro h
    refine Equiv.ext fun k => Fin.ext ?_
    rw [stdPerm_apply, Equiv.trans_apply, Fin.revPerm_apply]
    have := congrArg (fun e => ((e (k.rev) : Fin n) : ℕ)) h
    rw [coStdPerm_apply, coStd_eq_std_wordReverse, Fin.rev_rev] at this
    exact this
  · intro h
    refine Equiv.ext fun i => Fin.ext ?_
    rw [coStdPerm_apply, coStd_eq_std_wordReverse]
    have := congrArg (fun e => ((e i.rev : Fin n) : ℕ)) h
    rw [stdPerm_apply, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_rev] at this
    exact this

end CoStdPerm

/-! ### The inverse descent set of the mirrored permutation -/

/-- **Mirroring the positions of a permutation complements its inverse descent set**, with no
reflection: `Des((σ ∘ rev)⁻¹) = \{1, …, n-1\} ∖ Des(σ⁻¹)`.

The inverse of `σ ∘ rev` is `rev ∘ σ⁻¹`, so its two values across a step are the mirrors of those of
`σ⁻¹`, in the opposite order. This is *not* `HJO.Sym.invDescentSet_trans_revPerm`, which mirrors
the *values* of `σ` and therefore complements and reflects. -/
theorem invDescentSet_revPerm_trans {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    invDescentSet (Fin.revPerm.trans σ) = Ico 1 n \ invDescentSet σ := by
  ext r
  simp only [mem_sdiff, mem_Ico]
  constructor
  · intro hr
    obtain ⟨h1, h2, -⟩ := mem_descentSet.1 hr
    refine ⟨⟨h1, h2⟩, ?_⟩
    rw [mem_invDescentSet_iff σ h1 h2]
    rw [mem_invDescentSet_iff _ h1 h2] at hr
    have e : ∀ k : Fin n, ((Fin.revPerm.trans σ).symm k : Fin n) = (σ.symm k).rev := fun k => rfl
    rw [e, e, Fin.rev_lt_rev] at hr
    exact asymm hr
  · rintro ⟨⟨h1, h2⟩, hr⟩
    rw [mem_invDescentSet_iff σ h1 h2] at hr
    rw [mem_invDescentSet_iff _ h1 h2]
    have e : ∀ k : Fin n, ((Fin.revPerm.trans σ).symm k : Fin n) = (σ.symm k).rev := fun k => rfl
    rw [e, e, Fin.rev_lt_rev]
    have hne : (σ.symm ⟨r - 1, by omega⟩ : Fin n) ≠ σ.symm ⟨r, h2⟩ := fun hc =>
      absurd (σ.symm.injective hc) (Fin.ne_of_val_ne (show r - 1 ≠ r by omega))
    exact lt_of_le_of_ne (not_lt.1 hr) hne

end HJO.Sym

namespace HJO.ParkingFunctions

open HJO.Sym

variable {n : ℕ}

/-- **A standardisation fibre is a fundamental.**
`∑_{w : Std(w) = σ}x_w = F_{n,Des(σ⁻¹)}`, stated after truncation to the first `m` letters: the sum
over the words of the fibre with letters among the first `m` is `tr_m(F_{n,Des(σ⁻¹)})`, for every
`m`, and by `HJO.Sym.ext_letterTrunc` that family determines the identity.

The bijection is `w ↦ w ∘ σ⁻¹`, which lists the letters of `w` in the order `σ` ranks them; it
preserves the monomial, the two products having the same factors in a different order, and
`HJO.Sym.isAscendingWord_comp_symm_iff` says it carries the fibre onto the ascending words. -/
@[hjo "lem_cm_std_fibre"]
theorem sum_wordMonomial_stdPerm (K : Type*) [CommRing K] (σ : Equiv.Perm (Fin n)) (m : ℕ) :
    ∑ w ∈ {w ∈ Fintype.piFinset fun _ : Fin n => range m | stdPerm w = σ}, wordMonomial K w
      = Sym.letterTrunc K m (gessel K n (invDescentSet σ)) := by
  classical
  rw [letterTrunc_gessel K (invDescentSet_subset_Ico σ) m]
  refine Finset.sum_nbij' (fun w => w ∘ σ.symm) (fun a => a ∘ σ) (fun w hw => ?_) (fun a ha => ?_)
    (fun w _ => ?_) (fun a _ => ?_) fun w hw => ?_
  · rw [mem_filter, Fintype.mem_piFinset] at hw
    refine mem_boundedWords.2 ⟨(isAscendingWord_comp_symm_iff σ w).2 hw.2, fun k => ?_⟩
    exact mem_range.1 (hw.1 (σ.symm k))
  · rw [mem_boundedWords] at ha
    refine mem_filter.2 ⟨Fintype.mem_piFinset.2 fun k => mem_range.2 (ha.2 (σ k)), ?_⟩
    refine (isAscendingWord_comp_symm_iff σ (a ∘ σ)).1 ?_
    have h : (a ∘ σ) ∘ σ.symm = a := funext fun k => by simp
    rw [h]
    exact ha.1
  · exact funext fun i => by simp
  · exact funext fun k => by simp
  · rw [wordMonomial_eq_monomial, wordExponent_comp_equiv]

/-- The coefficientwise reading of `HJO.ParkingFunctions.sum_wordMonomial_stdPerm`: a monomial
occurs in `F_{n,Des(σ⁻¹)}` exactly when some word of the fibre of `σ` carries it, and then with
coefficient `1`. -/
theorem coeff_gessel_invDescentSet_eq_one (K : Type*) [CommRing K] {σ : Equiv.Perm (Fin n)}
    {d : ℕ →₀ ℕ} (h : ∃ w : Fin n → ℕ, stdPerm w = σ ∧ Sym.wordExponent w = d) :
    MvPowerSeries.coeff d (gessel K n (invDescentSet σ)) = 1 := by
  obtain ⟨w, hw, rfl⟩ := h
  rw [← wordExponent_comp_equiv σ.symm w]
  exact coeff_wordExponent_gessel K (invDescentSet_subset_Ico σ)
    ((isAscendingWord_comp_symm_iff σ w).2 hw)

/-- The other half of the coefficientwise reading: a monomial carried by no word of the fibre does
not occur. -/
theorem coeff_gessel_invDescentSet_eq_zero (K : Type*) [CommRing K] {σ : Equiv.Perm (Fin n)}
    {d : ℕ →₀ ℕ} (h : ¬ ∃ w : Fin n → ℕ, stdPerm w = σ ∧ Sym.wordExponent w = d) :
    MvPowerSeries.coeff d (gessel K n (invDescentSet σ)) = 0 := by
  refine coeff_gessel_eq_zero_of_forall_ne K fun a ha hd => h ⟨a ∘ σ, ?_, ?_⟩
  · refine (isAscendingWord_comp_symm_iff σ (a ∘ σ)).1 ?_
    have hc : (a ∘ σ) ∘ σ.symm = a := funext fun k => by simp
    rw [hc]
    exact ha
  · rw [wordExponent_comp_equiv, hd]

/-- **A co-standardisation fibre is a complemented fundamental.**
`∑_{w : Std⁻(w) = σ}x_w = F_{n,\{1,…,n-1\}∖Des(σ⁻¹)}`, stated after truncation as for
`HJO.ParkingFunctions.sum_wordMonomial_stdPerm`.

Reversing the word turns the co-standardisation fibre of `σ` into the standardisation fibre of
`σ ∘ rev` and fixes every monomial, and the inverse descent set of `σ ∘ rev` is the complement of
that of `σ`. -/
@[hjo "lem_om_costd_fibre"]
theorem sum_wordMonomial_coStdPerm (K : Type*) [CommRing K] (σ : Equiv.Perm (Fin n)) (m : ℕ) :
    ∑ w ∈ {w ∈ Fintype.piFinset fun _ : Fin n => range m | coStdPerm w = σ}, wordMonomial K w
      = Sym.letterTrunc K m (gessel K n (Ico 1 n \ invDescentSet σ)) := by
  classical
  rw [← invDescentSet_revPerm_trans σ, ← sum_wordMonomial_stdPerm K (Fin.revPerm.trans σ) m]
  refine Finset.sum_nbij' wordReverse wordReverse (fun w hw => ?_) (fun v hv => ?_)
    (fun w _ => wordReverse_wordReverse w) (fun v _ => wordReverse_wordReverse v) fun w _ => ?_
  · rw [mem_filter, Fintype.mem_piFinset] at hw ⊢
    exact ⟨fun k => hw.1 k.rev, coStdPerm_eq_iff_stdPerm_wordReverse.1 hw.2⟩
  · rw [mem_filter, Fintype.mem_piFinset] at hv ⊢
    refine ⟨fun k => hv.1 k.rev, coStdPerm_eq_iff_stdPerm_wordReverse.2 ?_⟩
    rw [wordReverse_wordReverse]
    exact hv.2
  · rw [wordMonomial, wordMonomial]
    exact (Fintype.prod_equiv Fin.revPerm _ _ fun k => rfl).symm

end HJO.ParkingFunctions
