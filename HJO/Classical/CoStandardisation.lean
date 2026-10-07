/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Classical.Standardisation
public import HJO.Paths.ReverseDescent
public meta import HJO.Attr

/-! # Co-standardisation, and reversing the values of a permutation

Standardisation breaks a tie between two equal letters in favour of the earlier position; the
co-standardisation `Std⁻` of `HJO.Sym.coStd` breaks it in favour of the later one. Everything about
it is read off the standardisation of the reversed word, so no property of the standardisation is
proved twice: this file does that reading, and then the two lemmas about reversing the *values* of a
permutation, which is where the complementation of a descent set comes from.

## Main definitions

* `HJO.Sym.invDescentSet`: `Des(σ⁻¹)`, the inverse descent set of a permutation of the positions.

## Main statements

* `HJO.Sym.coStd_eq_std_wordReverse`.
* `HJO.Sym.coStd_bijective`.
* `HJO.Sym.coStd_lt_coStd_iff`.
* `HJO.Sym.descentSet_coStd_subset_iff`.
* `HJO.Dyck.invNumber_add_invNumber_revPerm`.
* `HJO.Sym.invDescentSet_trans_revPerm`.

## Implementation notes

Positions are `0`-based, so the mirror `i ↦ n + 1 - i` is `Fin.rev`, and the identity
`Std⁻(w)_i = Std(w^R)_{n+1-i}` is `coStd w i = std (wordReverse w) i.rev`. Both statistics are the
usual `1`-based rank lowered by one, which is what makes that a literal equality rather than an
equality up to an offset.

`HJO.Dyck.invNumber_add_invNumber_revPerm` is stated additively, `inv(R,σ) + inv(R,σ^{rv}) = #R`,
and not as `inv(R,σ^{rv}) = #R - inv(R,σ)`: the subtraction is a genuine one in `ℤ` but would be
truncated in `ℕ`, and the additive form is the partition of `R` the proof produces. The two are
equivalent, `inv(R,σ) ≤ #R` being `HJO.Dyck.invNumber_le_card`.

`σ^{rv}`, the tuple `i ↦ n+1-σ_i`, is `σ.trans Fin.revPerm`; the remark that it is an
involution of the permutations is `Fin.revPerm`'s own involutivity.

The inverse descent set is read through `HJO.Sym.finWord`, the values of `σ⁻¹` extended off the
window by `0`; `HJO.Sym.mem_invDescentSet_iff` is the only interface to it that the proofs use, and
it never mentions the extension.

## References

This file proves `HJO.Sym.coStd_eq_std_wordReverse`, `HJO.Sym.coStd_bijective`,
`HJO.Sym.coStd_lt_coStd_iff`, `HJO.Sym.descentSet_coStd_subset_iff`,
`HJO.Dyck.invNumber_add_invNumber_revPerm` and `HJO.Sym.invDescentSet_trans_revPerm`, the inputs to
the involution on characteristic functions. -/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### The co-standardisation is the standardisation of the reversed word -/

section CoStd

variable {α : Type*} [LinearOrder α] {n : ℕ}

/-- **Co-standardisation is standardisation of the reversed word.**
`Std⁻(w)_i = Std(w^R)_{n+1-i}`, which with `0`-based positions is
`coStd w i = std (w^R) i.rev`.

The mirror `j ↦ n+1-j` is a bijection of the positions carrying `w^R_{n+1-j} = w_j`, so it matches
the two counts of smaller letters, and turns "at or after `i`" into "at or before `i.rev`". -/
@[hjo "lem_om_costd_reverse"]
theorem coStd_eq_std_wordReverse (w : Fin n → α) (i : Fin n) :
    coStd w i = std (wordReverse w) i.rev := by
  have hA : #{j | w j < w i} = #{j | wordReverse w j < wordReverse w i.rev} :=
    Finset.card_equiv Fin.revPerm fun a => by
      simp only [mem_filter, mem_univ, true_and, Fin.revPerm_apply, wordReverse_apply, Fin.rev_rev]
  have hB : #{j | i ≤ j ∧ w j = w i}
      = #{j | j ≤ i.rev ∧ wordReverse w j = wordReverse w i.rev} :=
    Finset.card_equiv Fin.revPerm fun a => by
      simp only [mem_filter, mem_univ, true_and, Fin.revPerm_apply, wordReverse_apply, Fin.rev_rev,
        Fin.rev_le_rev]
  rw [coStd, std, hA, hB]

/-- **Co-standardisation is a permutation.** `Std⁻(w)` is a bijection from the
`n` positions to themselves: it is the bijection `Std(w^R)` precomposed with the mirror. -/
@[hjo "lem_om_costd_perm"]
theorem coStd_bijective (w : Fin n → α) :
    Function.Bijective fun i => (⟨coStd w i, coStd_lt w i⟩ : Fin n) := by
  have hcomp : (fun i => (⟨coStd w i, coStd_lt w i⟩ : Fin n))
      = (fun k => (⟨std (wordReverse w) k, std_lt (wordReverse w) k⟩ : Fin n)) ∘ Fin.rev :=
    funext fun i => Fin.ext (coStd_eq_std_wordReverse w i)
  rw [hcomp]
  exact (std_bijective (wordReverse w)).comp Fin.rev_bijective

/-- The co-standardisation is injective, being a bijection. -/
theorem coStd_injective (w : Fin n → α) : Function.Injective (coStd w) := fun _ _ hij =>
  (coStd_bijective w).1 (Fin.ext hij)

/-- **The adjacent steps of a co-standardisation.** `Std⁻(w)` increases across
a step exactly when `w` increases *strictly* there — the tie-breaking clause now runs the other way,
so equal adjacent letters give a descent rather than an ascent. -/
@[hjo "lem_om_costd_step"]
theorem coStd_lt_coStd_iff (w : Fin n → α) {k l : Fin n} (hkl : (k : ℕ) + 1 = (l : ℕ)) :
    coStd w k < coStd w l ↔ w k < w l := by
  have hkl' : k < l := Fin.lt_def.2 (by omega)
  have hlk : l.rev < k.rev := Fin.rev_lt_rev.2 hkl'
  rw [coStd_eq_std_wordReverse, coStd_eq_std_wordReverse,
    std_lt_std_iff (wordReverse w) k.rev l.rev]
  simp only [wordReverse_apply, Fin.rev_rev]
  exact ⟨fun h => h.elim id fun h' => absurd h'.2 (asymm hlk), Or.inl⟩

/-- **Blockwise strict increase is a descent condition on the
co-standardisation.** `Des(Std⁻(w)) ⊆ T` holds exactly when `w` increases strictly across every step
outside `T`. -/
@[hjo "lem_om_costd_block"]
theorem descentSet_coStd_subset_iff (T : Finset ℕ) (w : Fin n → α) :
    descentSet n (finWord (coStd w)) ⊆ T ↔
      ∀ k l : Fin n, (k : ℕ) + 1 = (l : ℕ) → (l : ℕ) ∉ T → w k < w l := by
  constructor
  · intro hsub k l hkl hl
    by_contra hlt
    refine hl (hsub (mem_descentSet.2 ⟨by omega, l.isLt, ?_⟩))
    rw [finWord_of_lt _ l.isLt, finWord_of_lt _ (by omega : (l : ℕ) - 1 < n),
      show (⟨(l : ℕ), l.isLt⟩ : Fin n) = l from rfl,
      show (⟨(l : ℕ) - 1, by omega⟩ : Fin n) = k from
        Fin.ext (show (l : ℕ) - 1 = (k : ℕ) by omega)]
    have hne : coStd w l ≠ coStd w k := fun h =>
      absurd (coStd_injective w h) (Fin.ne_of_val_ne (by omega))
    have hnot : ¬ coStd w k < coStd w l := fun h => hlt ((coStd_lt_coStd_iff w hkl).1 h)
    omega
  · intro hmono j hj
    obtain ⟨h1, h2, h3⟩ := mem_descentSet.1 hj
    by_contra hjT
    have hk : j - 1 < n := by omega
    rw [finWord_of_lt _ h2, finWord_of_lt _ hk] at h3
    have hstep := hmono ⟨j - 1, hk⟩ ⟨j, h2⟩ (show j - 1 + 1 = j by omega) hjT
    exact absurd ((coStd_lt_coStd_iff w (show j - 1 + 1 = j by omega)).2 hstep) (asymm h3)

end CoStd

/-! ### The inverse descent set of a permutation of the positions -/

section InvDescent

variable {n : ℕ}

/-- `Des(σ⁻¹)`, the inverse descent set of a permutation `σ` of the `n` positions: the descent set
of the word `r ↦ σ⁻¹(r)`, read through `HJO.Sym.finWord`. It is the index set of the fundamental
quasisymmetric function attached to `σ` by `HJO.ParkingFunctions.sum_wordMonomial_stdPerm`. -/
def invDescentSet (σ : Equiv.Perm (Fin n)) : Finset ℕ :=
  descentSet n (finWord fun r => ((σ.symm r : Fin n) : ℕ))

/-- **Membership in the inverse descent set**: the step `j` of the window is a descent of `σ⁻¹`
exactly when `σ⁻¹` decreases across it. This is the only interface the proofs use, and it never
mentions the extension off the window. -/
theorem mem_invDescentSet_iff (σ : Equiv.Perm (Fin n)) {j : ℕ} (h1 : 1 ≤ j) (h2 : j < n) :
    j ∈ invDescentSet σ ↔
      (σ.symm ⟨j, h2⟩ : Fin n) < σ.symm ⟨j - 1, by omega⟩ := by
  rw [invDescentSet, mem_descentSet, finWord_of_lt _ h2, finWord_of_lt _ (by omega : j - 1 < n)]
  exact ⟨fun h => Fin.lt_def.2 h.2.2, fun h => ⟨h1, h2, Fin.lt_def.1 h⟩⟩

/-- The inverse descent set lies in the window of steps. -/
theorem invDescentSet_subset_Ico (σ : Equiv.Perm (Fin n)) : invDescentSet σ ⊆ Ico 1 n :=
  descentSet_subset_Ico n _

/-- **Reversing the values reverse-complements the inverse descent set.**
`Des((σ^{rv})⁻¹) = (\{1, …, n-1\} ∖ Des(σ⁻¹))^{∨n}`.

The inverse of `σ^{rv}` is `σ⁻¹` precomposed with the mirror, so its step `i` reads the two values
of `σ⁻¹` at the mirrored steps in the opposite order: the step `i` is a descent of `(σ^{rv})⁻¹`
exactly when the step `n - i` is *not* a descent of `σ⁻¹`. -/
@[hjo "lem_cm_reverse_perm_des"]
theorem invDescentSet_trans_revPerm (σ : Equiv.Perm (Fin n)) :
    invDescentSet (σ.trans Fin.revPerm)
      = ParkingFunctions.descentReverse n (Ico 1 n \ invDescentSet σ) := by
  have hrv : ∀ {j : ℕ} (h1 : 1 ≤ j) (h2 : j < n),
      (j ∈ invDescentSet (σ.trans Fin.revPerm)) ↔ n - j ∉ invDescentSet σ := by
    intro j h1 h2
    have hnj1 : 1 ≤ n - j := by omega
    have hnj2 : n - j < n := by omega
    rw [mem_invDescentSet_iff _ h1 h2, mem_invDescentSet_iff σ hnj1 hnj2]
    have e1 : ((σ.trans Fin.revPerm).symm ⟨j, h2⟩ : Fin n)
        = σ.symm ⟨n - 1 - j, by omega⟩ := by
      refine congrArg σ.symm (Fin.ext ?_)
      change ((⟨j, h2⟩ : Fin n).rev : ℕ) = n - 1 - j
      rw [Fin.val_rev]
      change n - (j + 1) = n - 1 - j
      omega
    have e2 : ((σ.trans Fin.revPerm).symm ⟨j - 1, by omega⟩ : Fin n)
        = σ.symm ⟨n - j, hnj2⟩ := by
      refine congrArg σ.symm (Fin.ext ?_)
      change ((⟨j - 1, by omega⟩ : Fin n).rev : ℕ) = n - j
      rw [Fin.val_rev]
      change n - (j - 1 + 1) = n - j
      omega
    have e3 : (⟨n - j - 1, by omega⟩ : Fin n) = ⟨n - 1 - j, by omega⟩ :=
      Fin.ext (show n - j - 1 = n - 1 - j by omega)
    rw [e1, e2, e3]
    have hne : (σ.symm ⟨n - 1 - j, by omega⟩ : Fin n) ≠ σ.symm ⟨n - j, hnj2⟩ := fun h =>
      absurd (σ.symm.injective h) (Fin.ne_of_val_ne (show n - 1 - j ≠ n - j by omega))
    exact ⟨fun h hc => absurd h (asymm hc), fun h => lt_of_le_of_ne (not_lt.1 h) hne⟩
  ext i
  simp only [ParkingFunctions.mem_descentReverse, mem_sdiff, mem_Ico]
  constructor
  · intro hi
    have h1 := (mem_descentSet.1 hi).1
    have h2 := (mem_descentSet.1 hi).2.1
    exact ⟨n - i, ⟨⟨by omega, by omega⟩, by
      have := (hrv h1 h2).1 hi
      exact this⟩, by omega⟩
  · rintro ⟨j, ⟨⟨hj1, hj2⟩, hjD⟩, rfl⟩
    have h1 : 1 ≤ n - j := by omega
    have h2 : n - j < n := by omega
    refine (hrv h1 h2).2 ?_
    rwa [show n - (n - j) = j from by omega]

end InvDescent

end HJO.Sym

namespace HJO.Dyck

/-- **Reversing the values of a permutation.**
`inv(R, σ) + inv(R, σ^{rv}) = #R` for every set `R` of increasing pairs of positions and every
bijection `σ` of them: each pair of `R` has its two values distinct, so it is inverted by exactly
one of `σ` and `σ^{rv}`.

Informally this reads `inv(R, σ^{rv}) = #R - inv(R, σ)`; the additive form is stated instead,
the subtraction being truncated in `ℕ`. The two are equivalent by
`HJO.Dyck.invNumber_le_card`. -/
@[hjo "lem_cm_reverse_perm_inv"]
theorem invNumber_add_invNumber_revPerm {n : ℕ} (R : Finset (Fin n × Fin n))
    (hR : ∀ p ∈ R, p.1 < p.2) {σ : Fin n → Fin n} (hσ : Function.Injective σ) :
    invNumber R σ + invNumber R (fun i => (σ i).rev) = #R := by
  classical
  have hsplit : invSet R (fun i => (σ i).rev) = {p ∈ R | ¬ σ p.2 < σ p.1} := by
    rw [invSet]
    refine Finset.filter_congr fun p hp => ?_
    have hne : σ p.1 ≠ σ p.2 := fun h => absurd (hσ h) (Fin.ne_of_val_ne (by
      have := hR p hp
      omega))
    rw [Fin.rev_lt_rev]
    exact ⟨fun h => asymm h, fun h => lt_of_le_of_ne (not_lt.1 h) hne⟩
  rw [invNumber, invNumber, invSet, hsplit]
  exact Finset.card_filter_add_card_filter_not (s := R) _

end HJO.Dyck
