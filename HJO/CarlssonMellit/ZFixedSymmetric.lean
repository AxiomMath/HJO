/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.AdjacentSwaps
public import HJO.CarlssonMellit.ZSubring
public meta import HJO.Attr

/-! # Fixed by the adjacent interchanges is symmetric

A member of `Z^{(k+1)}` fixed by every interchange `ŝ_m` of two adjacent letters at or above a
threshold is fixed by every finitary relabelling `ŝ_ρ` of the letters that moves nothing below that
threshold. This is `HJO.Sym.zPerm_eq_self_of_forall_zSwap_eq_self`, and it is the step that turns
the one-transposition invariance the class decomposition supplies into honest symmetry in the free
variables.

The mathematics is `Equiv.Perm.mem_mclosure_swap_succ` of
`HJO.AdjacentSwaps` — transported from the offsets `ℕ` to the letters `Option ℕ` along the
bijection `HJO.Sym.zLetter`, together with `HJO.Sym.zPerm_zPerm`: the relabellings compose, so a
permutation written as a product of adjacent interchanges acts as the composite of the
corresponding `ŝ_m`, each of which fixes the series.

## Main definitions

* `HJO.Sym.zLetterEquiv`: the bijection `ℕ ≃ Option ℕ` between the offsets from the level and the
  letters of the merged alphabet, of which `HJO.Sym.zLetter` is the forward map.
* `HJO.Sym.zLetterPerm`: a permutation of the offsets read as a permutation of the letters.

## Main results

* `HJO.Sym.zPerm_eq_self_of_forall_zSwap_eq_self`.

## Implementation notes

*The threshold is an offset and therefore an arbitrary natural number.* The statement asks
`j₀ ≥ k` for a permutation of `{j ≥ k}`, and at the level `k + 1` the letters are indexed by
`j ≥ k + 1`, so the thresholds `j₀ ≥ k + 1` are exactly the offsets `t₀ = j₀ - (k + 1)` ranging over
all of `ℕ`. No `ℕ`-subtraction appears: the hypotheses are stated at the offsets directly, and
`HJO.Sym.zSwap K k t` is the `ŝ_{k+1+t}`.

*The permutation is an arbitrary permutation of the letters, with the two restrictions
as hypotheses.* `HJO.Sym.zPerm` is defined for every permutation of `Option ℕ`, as
`HJO.CarlssonMellit.ZRing` records; the `ρ` is one fixing every letter below the
threshold and all but finitely many letters, and those are the two hypotheses `hfix` and `hsupport`.
Finitary is essential and not a technicality — as noted at `HJO.Sym.zPerm` — because a
permutation moving infinitely many letters is not a product of adjacent interchanges and no limiting
process reaches it.

*The induction is over the submonoid, not the subgroup.* `Equiv.Perm.mem_mclosure_swap_succ` is
stated for `Submonoid.closure`, so no inverse is ever taken and the induction needs only that `ŝ_ρ`
is multiplicative in `ρ` (`HJO.Sym.zPerm_zPerm`) and trivial at the identity — not that it is
invertible. The membership hypothesis `F ∈ Z^{(k+1)}` is what those two statements require, and it
is carried through the induction because `ŝ_ρ` maps `Z^{(k+1)}` to itself.

## References

Lemma `HJO.Sym.zPerm_eq_self_of_forall_zSwap_eq_self`, using `HJO.Sym.zGraded`, `HJO.Sym.zPerm` and
`HJO.Sym.zSwap` and proved from `Equiv.Perm.mem_mclosure_swap_succ` and `HJO.Sym.zPerm_zPerm`;
consumed by `HJO.Dyck.existsUnique_eq_sum_pow_mul_realiseAddLetter`. E. Carlsson and A. Mellit, *A
proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 4, where the
symmetry is asserted without this argument.
-/

@[expose] public section

open MulAction

namespace HJO.Sym

/-! ### The offsets and the letters -/

/-- The bijection between the offsets from the level and the letters of the merged alphabet: offset
`0` is the distinguished letter `y_{k+1}` and offset `r + 1` is the letter `x_{r+1}`. Its forward
map is `HJO.Sym.zLetter`. -/
def zLetterEquiv : ℕ ≃ Option ℕ where
  toFun := zLetter
  invFun a := match a with
    | none => 0
    | some i => i + 1
  left_inv t := by cases t <;> rfl
  right_inv a := by cases a <;> rfl

@[simp] theorem zLetterEquiv_apply (t : ℕ) : zLetterEquiv t = zLetter t := rfl

@[simp]
theorem zLetterEquiv_symm_zLetter (t : ℕ) : zLetterEquiv.symm (zLetter t) = t :=
  zLetterEquiv.symm_apply_apply t

/-- A permutation of the offsets, read as a permutation of the letters of the merged alphabet. -/
def zLetterPerm (σ : Equiv.Perm ℕ) : Equiv.Perm (Option ℕ) :=
  (zLetterEquiv.symm.trans σ).trans zLetterEquiv

@[simp]
theorem zLetterPerm_zLetter (σ : Equiv.Perm ℕ) (t : ℕ) :
    zLetterPerm σ (zLetter t) = zLetter (σ t) := by
  rw [zLetterPerm, Equiv.trans_apply, Equiv.trans_apply, zLetterEquiv_symm_zLetter,
    zLetterEquiv_apply]

@[simp]
theorem zLetterPerm_one : zLetterPerm 1 = 1 :=
  Equiv.ext fun a => by
    rw [zLetterPerm, Equiv.trans_apply, Equiv.trans_apply]
    exact zLetterEquiv.apply_symm_apply a

@[simp]
theorem zLetterPerm_mul (σ τ : Equiv.Perm ℕ) :
    zLetterPerm (σ * τ) = zLetterPerm σ * zLetterPerm τ :=
  Equiv.ext fun a => by
    simp only [zLetterPerm, Equiv.trans_apply, Equiv.Perm.mul_apply, zLetterEquiv_apply,
      zLetterEquiv_symm_zLetter]

/-- An adjacent interchange of offsets is the interchange `HJO.Sym.zSwapEquiv` of the corresponding
two letters. -/
@[simp]
theorem zLetterPerm_swap_succ (m : ℕ) : zLetterPerm (Equiv.swap m (m + 1)) = zSwapEquiv m := by
  refine Equiv.ext fun a => ?_
  obtain ⟨t, rfl⟩ : ∃ t, a = zLetter t :=
    ⟨zLetterEquiv.symm a, (zLetterEquiv.apply_symm_apply a).symm⟩
  rw [zLetterPerm_zLetter, zSwapEquiv]
  rcases eq_or_ne t m with rfl | htm
  · rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
  rcases eq_or_ne t (m + 1) with rfl | htm'
  · rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
  · rw [Equiv.swap_apply_of_ne_of_ne htm htm',
      Equiv.swap_apply_of_ne_of_ne (fun h => htm (zLetter_injective h))
        fun h => htm' (zLetter_injective h)]

/-- Every permutation of the letters comes from a permutation of the offsets. -/
theorem exists_zLetterPerm (ρ : Equiv.Perm (Option ℕ)) : ∃ σ : Equiv.Perm ℕ, zLetterPerm σ = ρ :=
  ⟨(zLetterEquiv.trans ρ).trans zLetterEquiv.symm, Equiv.ext fun a => by
    change zLetterEquiv (zLetterEquiv.symm (ρ (zLetterEquiv (zLetterEquiv.symm a)))) = ρ a
    rw [zLetterEquiv.apply_symm_apply, zLetterEquiv.apply_symm_apply]⟩

/-! ### Fixed by the adjacent interchanges is symmetric -/

variable {K : Type*} [CommRing K] [IsDomain K] {k : ℕ} {F : AuxAlphabetSeriesFrac K (k + 1)}

/-- **Fixed by the adjacent interchanges is symmetric.** Let `F` lie in `Z^{(k+1)}` and be fixed by
`ŝ_m` for every `m` at or above a threshold, and let `ρ` be a permutation of the letters of the
merged alphabet fixing every letter below that threshold and all but finitely many letters. Then
`ŝ_ρ(F) = F`.

By `Equiv.Perm.mem_mclosure_swap_succ` the permutation is a product of finitely many adjacent
interchanges at or above the threshold — a product, not a word in the generators and their inverses,
the generators being involutions — and by `HJO.Sym.zPerm_zPerm` the relabellings compose, so `ŝ_ρ`
is the corresponding composite of the `ŝ_m`, each of which fixes `F`. -/
@[hjo "lem_cm_zfixed_symmetric"]
theorem zPerm_eq_self_of_forall_zSwap_eq_self (hF : F ∈ zRing K k) {t₀ : ℕ}
    (hswap : ∀ t, t₀ ≤ t → zSwap K k t F = F) {ρ : Equiv.Perm (Option ℕ)}
    (hfix : ∀ t < t₀, ρ (zLetter t) = zLetter t)
    (hsupport : (fixedBy (Option ℕ) ρ)ᶜ.Finite) : zPerm K k ρ F = F := by
  obtain ⟨σ, rfl⟩ := exists_zLetterPerm ρ
  have hfixσ : ∀ t < t₀, σ t = t := fun t ht =>
    zLetter_injective ((zLetterPerm_zLetter σ t).symm.trans (hfix t ht))
  have hsupportσ : (fixedBy ℕ σ)ᶜ.Finite := by
    refine Set.Finite.subset (hsupport.preimage zLetter_injective.injOn) fun t ht => ?_
    simp only [Set.mem_compl_iff, mem_fixedBy, Equiv.Perm.smul_def] at ht
    refine Set.mem_preimage.2 ?_
    simp only [Set.mem_compl_iff, mem_fixedBy, Equiv.Perm.smul_def, zLetterPerm_zLetter]
    exact fun h => ht (zLetter_injective h)
  have hσ := Equiv.Perm.mem_mclosure_swap_succ hfixσ hsupportσ
  clear hfix hsupport hfixσ hsupportσ
  induction hσ using Submonoid.closure_induction with
  | mem x h =>
    obtain ⟨m, hm, rfl⟩ := h
    rw [zLetterPerm_swap_succ, ← zSwap_apply]
    exact hswap m hm
  | one => rw [zLetterPerm_one, zPerm_one hF]
  | mul x y _ _ ihx ihy =>
    rw [zLetterPerm_mul, ← zPerm_zPerm _ _ hF, ihy, ihx]

end HJO.Sym
