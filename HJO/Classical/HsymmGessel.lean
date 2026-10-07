/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Classical.EsymmGessel
public import HJO.Classical.HsymmComposition
public import HJO.Symmetric.UkRegular
public meta import HJO.Attr

/-! # A complete homogeneous function is the fundamental of the empty descent set

`HJO.ParkingFunctions.realisation_completeHomog`: for a realisation `ι` and `r ≥ 1`,
`ι(h_r) = F_{r,∅}`.

## Main statements

* `HJO.Sym.isAscendingWord_empty_iff_monotone`: ascending with *no* strict step is monotonicity, so
  the words counted by `F_{r,∅}` are the weakly increasing ones.
* `HJO.ParkingFunctions.realisation_completeHomog`.

## Implementation notes

The proof runs in the shape of its `e`-side companion
`HJO.ParkingFunctions.realisation_elemSymm`: compare the two series after truncating to the first
`m` letters, for every `m`, and appeal to `HJO.Sym.ext_letterTrunc`.

Where the two sides differ is the recursion. Adding a letter to `e_n` contributes in one degree
only, so `HJO.CreationSeeds.elemSymm_add_letter` is already a two-term recursion; adding one to
`h_n` in every degree, and `HJO.CreationSeeds.completeHomog_add_letter` is the full geometric sum
`ψ(h_N) = ∑_{j≤N}a^jφ(h_{N-j})`. Peeling its `j = 0` term folds the rest back into `ψ(h_{N-1})` and
gives the two-term form `HJO.CreationSeeds.completeHomog_add_letter_succ`,
`ψ(h_{n+1}) = a ψ(h_n) + φ(h_{n+1})`, in which `ψ` — not `φ` — carries the shorter word. So the
induction is a double one: on the number of letters outside, and on the length inside, the inner
step consuming the outer hypothesis at one letter fewer and the inner hypothesis at one letter less
in the word.

The word side splits the same way: a weakly increasing word in `m + 1` letters either avoids the
letter `m`, and is then a word in `m` letters, or ends with it, and deleting that last entry leaves
a weakly increasing word of length one less *in the same `m + 1` letters* — the trailing block of
`m`'s being peeled one letter at a time rather than all at once, which is what makes the two
recursions match term by term.

## References

This file proves `HJO.ParkingFunctions.realisation_completeHomog`.
-/

@[expose] public section

open Finset

namespace HJO.CreationSeeds

section Letters

variable {K : Type*} [CommRing K] [Algebra ℚ K] {R : Type*} [CommRing R] [Algebra ℚ R]
  {F G : Type*} [FunLike F (Sym.Lambda K) R] [RingHomClass F (Sym.Lambda K) R]
  [FunLike G (Sym.Lambda K) R] [RingHomClass G (Sym.Lambda K) R]

/-- **Adding one letter, in two-term form.** If `ψ` exceeds `φ` by `aᵏ` on every power sum, then
`ψ(h_{n+1}) = a ψ(h_n) + φ(h_{n+1})`: peeling the `j = 0` term off the geometric sum of
`HJO.CreationSeeds.completeHomog_add_letter` leaves `a` times the same sum one degree down, which is
`ψ(h_n)`. -/
theorem completeHomog_add_letter_succ (f : F) (g : G) (a : R)
    (h : ∀ k : ℕ, 0 < k → g (Sym.powerSum K k) = f (Sym.powerSum K k) + a ^ k) (n : ℕ) :
    g (Sym.completeHomog K (n + 1))
      = a * g (Sym.completeHomog K n) + f (Sym.completeHomog K (n + 1)) := by
  have h1 := completeHomog_add_letter f g a h (n + 1)
  rw [Finset.sum_range_succ'] at h1
  simp only [pow_zero, one_mul, Nat.sub_zero, Nat.succ_sub_succ] at h1
  rw [h1, completeHomog_add_letter f g a h n, Finset.mul_sum]
  exact congrArg₂ _ (Finset.sum_congr rfl fun j _ => by rw [pow_succ]; ring) rfl

end Letters

end HJO.CreationSeeds

namespace HJO.Sym

/-! ### Weakly increasing words -/

/-- **Ascending with no strict step is monotonicity.** The empty descent set demands nothing beyond
weak increase, and that is exactly `Monotone`. -/
theorem isAscendingWord_empty_iff_monotone {N : ℕ} {w : Fin N → ℕ} :
    IsAscendingWord N ∅ w ↔ Monotone w :=
  ⟨fun h => h.monotone, fun h => ⟨h, fun _ _ _ hmem => absurd hmem (notMem_empty _)⟩⟩

/-- **Appending the letter `m` to a weakly increasing word bounded by `m + 1`** gives a weakly
increasing word bounded by `m + 1` whose last letter is `m`. Unlike the strictly increasing case,
the shorter word keeps the same bound: it may already end in `m`. -/
theorem snoc_mem_boundedWords_empty {n m : ℕ} {v : Fin n → ℕ}
    (hv : v ∈ boundedWords n ∅ (m + 1)) :
    Fin.snoc v m ∈ boundedWords (n + 1) ∅ (m + 1) := by
  obtain ⟨hasc, hlt⟩ := mem_boundedWords.1 hv
  have hmono := isAscendingWord_empty_iff_monotone.1 hasc
  refine mem_boundedWords.2 ⟨isAscendingWord_empty_iff_monotone.2 ?_, ?_⟩
  · refine Fin.monotone_iff_le_succ.2 fun i => ?_
    rw [Fin.snoc_castSucc]
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt i.isLt) with hi | hi
    · rw [show i.succ = Fin.last n from Fin.ext (by rw [Fin.val_succ, Fin.val_last]; omega),
        Fin.snoc_last]
      exact Nat.lt_succ_iff.1 (hlt i)
    · rw [show i.succ = (⟨(i : ℕ) + 1, by omega⟩ : Fin n).castSucc from Fin.ext (by simp),
        Fin.snoc_castSucc]
      exact hmono (Fin.mk_le_mk.2 (by simp))
  · refine Fin.lastCases ?_ fun i => ?_
    · rw [Fin.snoc_last]
      omega
    · rw [Fin.snoc_castSucc]
      exact hlt i

/-- **Dropping the last letter of a weakly increasing word that ends at `m`** gives a weakly
increasing word, still bounded by `m + 1`. -/
theorem init_mem_boundedWords_empty {n m : ℕ} {w : Fin (n + 1) → ℕ}
    (hw : w ∈ boundedWords (n + 1) ∅ (m + 1)) :
    Fin.init w ∈ boundedWords n ∅ (m + 1) := by
  obtain ⟨hasc, hlt⟩ := mem_boundedWords.1 hw
  have hmono := isAscendingWord_empty_iff_monotone.1 hasc
  refine mem_boundedWords.2 ⟨isAscendingWord_empty_iff_monotone.2 fun a b hab => ?_, fun k => ?_⟩
  · exact hmono (Fin.castSucc_le_castSucc_iff.2 hab)
  · exact hlt k.castSucc

/-- **The weakly increasing words in `m + 1` letters split by whether they end at `m`.** A word not
ending at `m` is bounded by `m`, a monotone word being bounded by its last letter; a word ending at
`m` loses that entry and becomes a weakly increasing word of length one less in the same `m + 1`
letters. This is the recursion `HJO.CreationSeeds.completeHomog_add_letter_succ` matches. -/
theorem sum_monomial_boundedWords_empty_succ (K : Type*) [CommRing K] (n m : ℕ) :
    ∑ w ∈ boundedWords (n + 1) ∅ (m + 1),
        (MvPowerSeries.monomial (wordExponent w) 1 : AlphabetSeries K)
      = (MvPowerSeries.X m : AlphabetSeries K)
          * ∑ v ∈ boundedWords n ∅ (m + 1),
              (MvPowerSeries.monomial (wordExponent v) 1 : AlphabetSeries K)
        + ∑ w ∈ boundedWords (n + 1) ∅ m,
            (MvPowerSeries.monomial (wordExponent w) 1 : AlphabetSeries K) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (boundedWords (n + 1) ∅ (m + 1))
    fun w => w (Fin.last n) = m]
  have hnot : {w ∈ boundedWords (n + 1) ∅ (m + 1) | ¬w (Fin.last n) = m}
      = boundedWords (n + 1) ∅ m := by
    ext w
    rw [mem_filter, mem_boundedWords_succ, mem_boundedWords_succ]
    exact ⟨fun h => ⟨h.1.1, by omega⟩, fun h => ⟨⟨h.1, by omega⟩, by omega⟩⟩
  have hbij : ∑ w ∈ {w ∈ boundedWords (n + 1) ∅ (m + 1) | w (Fin.last n) = m},
        (MvPowerSeries.monomial (wordExponent w) 1 : AlphabetSeries K)
      = ∑ v ∈ boundedWords n ∅ (m + 1),
          (MvPowerSeries.X m : AlphabetSeries K) * MvPowerSeries.monomial (wordExponent v) 1 := by
    refine Finset.sum_nbij' Fin.init (fun v => Fin.snoc v m) (fun w hw => ?_) (fun v hv => ?_)
      (fun w hw => ?_) (fun v _ => Fin.init_snoc _ _) fun w hw => ?_
    · exact init_mem_boundedWords_empty (mem_filter.1 hw).1
    · exact mem_filter.2 ⟨snoc_mem_boundedWords_empty hv, Fin.snoc_last _ _⟩
    · rw [mem_filter] at hw
      rw [← hw.2, Fin.snoc_init_self]
    · rw [mem_filter] at hw
      have hX : (MvPowerSeries.X m : AlphabetSeries K)
          = MvPowerSeries.monomial (Finsupp.single m 1) 1 := by
        rw [← MvPowerSeries.X_pow_eq m 1, pow_one]
      have hsnoc : Fin.snoc (Fin.init w) m = w := by rw [← hw.2, Fin.snoc_init_self]
      have hwe : wordExponent w = wordExponent (Fin.init w) + Finsupp.single m 1 := by
        conv_lhs => rw [← hsnoc]
        rw [wordExponent_snoc]
      rw [hX, MvPowerSeries.monomial_mul_monomial, one_mul, hwe, add_comm]
  rw [hnot, hbij, ← Finset.mul_sum]

end HJO.Sym

namespace HJO.ParkingFunctions

/-- **An algebra map killing every power sum kills every `h_n` with `n ≥ 1`**: Newton's identity
expresses `h_{n+1}` as a combination of products each carrying a power sum. This is the
base case `φ_0(h_n) = 0`. -/
theorem map_completeHomog_eq_zero {K : Type*} [CommRing K] [Algebra ℚ K] {R : Type*} [CommRing R]
    [Algebra K R] (φ : Sym.Lambda K →ₐ[K] R)
    (h : ∀ k : ℕ, 0 < k → φ (Sym.powerSum K k) = 0) {n : ℕ} (hn : 0 < n) :
    φ (Sym.completeHomog K n) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [UkRegular.completeHomog_succ, map_mul, map_sum]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun k _ => ?_)
  rw [map_mul, h (k + 1) k.succ_pos, zero_mul]

/-- **The truncated realisation of a complete homogeneous function counts the weakly increasing
words.** `tr_m(ι(h_n)) = ∑_{w ∈ W^{(m)}_{n,∅}}x_w`, by a double induction: one more letter adds
exactly the words that end with it, and those are read off the words of length one less in the same
letters. -/
theorem letterTrunc_realisation_completeHomog {K : Type*} [CommRing K] [Algebra ℚ K]
    {ι : Sym.Lambda K →ₐ[K] Sym.AlphabetSeries K} (hι : Sym.IsRealisation ι) (m : ℕ) :
    ∀ n : ℕ, Sym.letterTrunc K m (ι (Sym.completeHomog K n))
      = ∑ w ∈ Sym.boundedWords n ∅ m,
          (MvPowerSeries.monomial (Sym.wordExponent w) 1 : Sym.AlphabetSeries K) := by
  induction m with
  | zero =>
    intro n
    match n with
    | 0 =>
      rw [CopPower.completeHomog_zero, map_one, map_one, Sym.boundedWords_zero_eq_univ,
        Finset.univ_unique, Finset.sum_singleton, Sym.wordExponent_of_length_zero]
      simp
    | p + 1 =>
      rw [Sym.boundedWords_zero_letters, Finset.sum_empty]
      refine map_completeHomog_eq_zero ((Sym.letterTrunc K 0).comp ι) (fun k hk => ?_) p.succ_pos
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [AlgHom.comp_apply, Sym.letterTrunc_realisation_powerSum hι, Finset.range_zero,
        Finset.sum_empty]
  | succ m ih =>
    intro n
    induction n with
    | zero =>
      rw [CopPower.completeHomog_zero, map_one, map_one, Sym.boundedWords_zero_eq_univ,
        Finset.univ_unique, Finset.sum_singleton, Sym.wordExponent_of_length_zero]
      simp
    | succ p ihn =>
      rw [Sym.sum_monomial_boundedWords_empty_succ, ← ihn, ← ih (p + 1)]
      have hstep := CreationSeeds.completeHomog_add_letter_succ
        ((Sym.letterTrunc K m).comp ι : Sym.Lambda K →ₐ[K] Sym.AlphabetSeries K)
        ((Sym.letterTrunc K (m + 1)).comp ι : Sym.Lambda K →ₐ[K] Sym.AlphabetSeries K)
        (MvPowerSeries.X m : Sym.AlphabetSeries K)
        (fun k hk => by
          rw [AlgHom.comp_apply, AlgHom.comp_apply,
            Sym.letterTrunc_realisation_powerSum_succ hι m hk])
        p
      rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply] at hstep
      rw [hstep]

/-- **A complete homogeneous function is the fundamental of the empty descent
set.** `ι(h_r) = F_{r,∅}` for every realisation `ι` and every `r ≥ 1`.

Truncating to the first `m` letters turns the left side into a sum over the weakly increasing words
in those letters and the right side into the same sum, for every `m`; truncations separate the
alphabet series, so the two are equal. The usual hypothesis `r ≥ 1` is not needed: at
`r = 0` both sides are `1`, the empty word being the only word of length `0`. -/
@[hjo "lem_om_hsymm_gessel"]
theorem realisation_completeHomog {K : Type*} [CommRing K] [Algebra ℚ K]
    {ι : Sym.Lambda K →ₐ[K] Sym.AlphabetSeries K} (hι : Sym.IsRealisation ι) (r : ℕ) :
    ι (Sym.completeHomog K r) = gessel K r ∅ := by
  refine Sym.ext_letterTrunc.2 fun m => ?_
  rw [letterTrunc_realisation_completeHomog hι m r, letterTrunc_gessel K (empty_subset _) m]

end HJO.ParkingFunctions
