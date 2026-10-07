/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Classical.GesselTruncation
public import HJO.CreationSeeds.LogDeriv
public meta import HJO.Attr

/-! # An elementary symmetric function is the fundamental of the full descent set

`HJO.ParkingFunctions.realisation_elemSymm`: for a realisation `ι` and `r ≥ 1`,
`ι(e_r) = F_{r,\{1,…,r-1\}}`.

## Main statements

* `HJO.Sym.isAscendingWord_Ico_iff_strictMono`: ascending at *every* step is strict monotonicity, so
  the words counted by `F_{r,\{1,…,r-1\}}` are the strictly increasing ones.
* `HJO.ParkingFunctions.realisation_elemSymm`.

## Implementation notes

The proof is the standard one: compare the two series after truncating to the first `m` letters, for
every `m`, and appeal to `HJO.Sym.ext_letterTrunc`. On the left the truncations `φ_m = tr_m ∘ ι`
differ by one letter (`HJO.Sym.letterTrunc_realisation_powerSum_succ`), so
`HJO.CreationSeeds.elemSymm_add_letter` gives `φ_{m+1}(e_n) = φ_m(e_n) + x_m φ_m(e_{n-1})`; on the
right `HJO.ParkingFunctions.letterTrunc_gessel` turns the truncation into a sum over the strictly
increasing words in the first `m+1` letters, and that sum splits the same way — a word either avoids
the letter `m`, or carries it, necessarily in its last position.

The two base cases are `n = 0`, where both sides are `1` (the empty word is the only word of length
`0`, whatever the bound), and `m = 0`, where `φ_0` kills every power sum and hence every `e_n` with
`n ≥ 1`, while no word of positive length fits in no letters.

The split is a `Finset.sum_filter_add_sum_filter_not` on "the last letter is `m`", the filter's
complement being the words bounded by `m` because a monotone word is bounded by its last letter
(`HJO.Sym.mem_boundedWords_succ`). The bijection onto the shorter words is `Fin.init` against
`Fin.snoc · m`, and `HJO.Sym.wordExponent_snoc` is what turns the extra letter into the factor
`x_m`.

## References

This file proves `HJO.ParkingFunctions.realisation_elemSymm`.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### Strictly increasing words -/

/-- **Ascending at every step is strict monotonicity.** The full descent set `\{1, …, N-1\}` demands
a strict increase across every adjacent pair of positions, and that is exactly `StrictMono`. -/
theorem isAscendingWord_Ico_iff_strictMono {N : ℕ} {w : Fin N → ℕ} :
    IsAscendingWord N (Ico 1 N) w ↔ StrictMono w := by
  refine ⟨fun h => ?_, fun h => ⟨h.monotone, fun k l hkl _ => h (Fin.lt_def.2 (by omega))⟩⟩
  match N with
  | 0 => exact fun a _ _ => absurd a.isLt (Nat.not_lt_zero _)
  | p + 1 =>
    refine Fin.strictMono_iff_lt_succ.2 fun i => h.lt_of_mem i.castSucc i.succ ?_ ?_
    · rw [Fin.val_castSucc, Fin.val_succ]
    · rw [Fin.val_succ]
      exact mem_Ico.2 ⟨by omega, by omega⟩

/-- The exponent vector of the empty word is zero. -/
@[simp]
theorem wordExponent_of_length_zero (w : Fin 0 → ℕ) : wordExponent w = 0 := by
  simp [wordExponent]

/-- **Appending a letter adds it to the exponent vector.** -/
theorem wordExponent_snoc {n : ℕ} (v : Fin n → ℕ) (a : ℕ) :
    wordExponent (Fin.snoc v a) = wordExponent v + Finsupp.single a 1 := by
  rw [wordExponent, wordExponent, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- **There is exactly one word of length zero**, whatever the descent set and whatever the bound:
the empty tuple, which is ascending and has no letter to bound. -/
theorem boundedWords_zero_eq_univ (S : Finset ℕ) (m : ℕ) :
    boundedWords 0 S m = univ :=
  eq_univ_of_forall fun _w =>
    mem_boundedWords.2 ⟨⟨fun a _ _ => absurd a.isLt (Nat.not_lt_zero _),
      fun k _ _ _ => absurd k.isLt (Nat.not_lt_zero _)⟩,
      fun k => absurd k.isLt (Nat.not_lt_zero _)⟩

/-- **No word of positive length fits in no letters.** -/
theorem boundedWords_zero_letters {n : ℕ} (S : Finset ℕ) :
    boundedWords (n + 1) S 0 = ∅ :=
  eq_empty_of_forall_notMem fun _w hw =>
    absurd ((mem_boundedWords.1 hw).2 0) (Nat.not_lt_zero _)

/-- **Appending the letter `m` to a strictly increasing word bounded by `m`** gives a strictly
increasing word bounded by `m + 1` whose last letter is `m`. -/
theorem snoc_mem_boundedWords {n m : ℕ} {v : Fin n → ℕ} (hv : v ∈ boundedWords n (Ico 1 n) m) :
    Fin.snoc v m ∈ boundedWords (n + 1) (Ico 1 (n + 1)) (m + 1) := by
  obtain ⟨hasc, hlt⟩ := mem_boundedWords.1 hv
  refine mem_boundedWords.2 ⟨isAscendingWord_Ico_iff_strictMono.2 ?_, ?_⟩
  · refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    rw [Fin.snoc_castSucc]
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt i.isLt) with hi | hi
    · rw [show i.succ = Fin.last n from Fin.ext (by rw [Fin.val_succ, Fin.val_last]; omega),
        Fin.snoc_last]
      exact hlt i
    · rw [show i.succ = (⟨(i : ℕ) + 1, by omega⟩ : Fin n).castSucc from Fin.ext (by simp),
        Fin.snoc_castSucc]
      exact isAscendingWord_Ico_iff_strictMono.1 hasc (Fin.lt_def.2 (by simp))
  · refine Fin.lastCases ?_ fun i => ?_
    · rw [Fin.snoc_last]
      omega
    · rw [Fin.snoc_castSucc]
      exact Nat.lt_succ_of_lt (hlt i)

/-- **Dropping the last letter of a strictly increasing word that ends at `m`** gives a strictly
increasing word bounded by `m`. -/
theorem init_mem_boundedWords {n m : ℕ} {w : Fin (n + 1) → ℕ}
    (hw : w ∈ boundedWords (n + 1) (Ico 1 (n + 1)) (m + 1)) (hlast : w (Fin.last n) = m) :
    Fin.init w ∈ boundedWords n (Ico 1 n) m := by
  obtain ⟨hasc, -⟩ := mem_boundedWords.1 hw
  have hmono := isAscendingWord_Ico_iff_strictMono.1 hasc
  refine mem_boundedWords.2 ⟨isAscendingWord_Ico_iff_strictMono.2 fun a b hab => ?_, fun k => ?_⟩
  · exact hmono (Fin.lt_def.2 (by simpa using Fin.lt_def.1 hab))
  · rw [Fin.init, ← hlast]
    exact hmono (Fin.lt_def.2 (by rw [Fin.val_castSucc, Fin.val_last]; omega))

/-- **The words in `m + 1` letters split by whether they use the letter `m`.** For strictly
increasing words the letter `m`, if used at all, is the last one, so deleting it is a bijection onto
the strictly increasing words of length one less in `m` letters; and a word not using it is bounded
by `m`. This is the recursion `HJO.CreationSeeds.elemSymm_add_letter` matches. -/
theorem sum_monomial_boundedWords_succ (K : Type*) [CommRing K] (n m : ℕ) :
    ∑ w ∈ boundedWords (n + 1) (Ico 1 (n + 1)) (m + 1),
        (MvPowerSeries.monomial (wordExponent w) 1 : AlphabetSeries K)
      = (∑ w ∈ boundedWords (n + 1) (Ico 1 (n + 1)) m,
          (MvPowerSeries.monomial (wordExponent w) 1 : AlphabetSeries K))
        + (MvPowerSeries.X m : AlphabetSeries K)
          * ∑ v ∈ boundedWords n (Ico 1 n) m,
              (MvPowerSeries.monomial (wordExponent v) 1 : AlphabetSeries K) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (boundedWords (n + 1) (Ico 1 (n + 1)) (m + 1))
    fun w => w (Fin.last n) = m]
  have hnot : {w ∈ boundedWords (n + 1) (Ico 1 (n + 1)) (m + 1) | ¬w (Fin.last n) = m}
      = boundedWords (n + 1) (Ico 1 (n + 1)) m := by
    ext w
    rw [mem_filter, mem_boundedWords_succ, mem_boundedWords_succ]
    exact ⟨fun h => ⟨h.1.1, by omega⟩, fun h => ⟨⟨h.1, by omega⟩, by omega⟩⟩
  have hbij : ∑ w ∈ {w ∈ boundedWords (n + 1) (Ico 1 (n + 1)) (m + 1) | w (Fin.last n) = m},
        (MvPowerSeries.monomial (wordExponent w) 1 : AlphabetSeries K)
      = ∑ v ∈ boundedWords n (Ico 1 n) m,
          (MvPowerSeries.X m : AlphabetSeries K) * MvPowerSeries.monomial (wordExponent v) 1 := by
    refine Finset.sum_nbij' Fin.init (fun v => Fin.snoc v m) (fun w hw => ?_) (fun v hv => ?_)
      (fun w hw => ?_) (fun v _ => Fin.init_snoc _ _) fun w hw => ?_
    · rw [mem_filter] at hw
      exact init_mem_boundedWords hw.1 hw.2
    · exact mem_filter.2 ⟨snoc_mem_boundedWords hv, Fin.snoc_last _ _⟩
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
  rw [hnot, hbij, ← Finset.mul_sum, add_comm]

end HJO.Sym

namespace HJO.ParkingFunctions

/-- **An algebra map killing every power sum kills every `e_n` with `n ≥ 1`**: Newton's identity
expresses `e_{n+1}` as a combination of products each carrying a power sum. This is the
base case `φ_0(e_n) = 0`. -/
theorem map_elemSymm_eq_zero {K : Type*} [CommRing K] [Algebra ℚ K] {R : Type*} [CommRing R]
    [Algebra K R] (φ : Sym.Lambda K →ₐ[K] R)
    (h : ∀ k : ℕ, 0 < k → φ (Sym.powerSum K k) = 0) {n : ℕ} (hn : 0 < n) :
    φ (Sym.elemSymm K n) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Sym.elemSymm, map_mul, map_sum]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun k _ => ?_)
  rw [map_mul, map_mul, h (k + 1) k.succ_pos, mul_zero, zero_mul]

/-- **The truncated realisation of an elementary symmetric function counts the strictly increasing
words.** `tr_m(ι(e_n)) = ∑_{w ∈ W^{(m)}_{n,\{1,…,n-1\}}}x_w`, by induction on the number of
letters: one more letter adds exactly the words that use it. -/
theorem letterTrunc_realisation_elemSymm {K : Type*} [CommRing K] [Algebra ℚ K]
    {ι : Sym.Lambda K →ₐ[K] Sym.AlphabetSeries K} (hι : Sym.IsRealisation ι) (m : ℕ) :
    ∀ n : ℕ, Sym.letterTrunc K m (ι (Sym.elemSymm K n))
      = ∑ w ∈ Sym.boundedWords n (Ico 1 n) m,
          (MvPowerSeries.monomial (Sym.wordExponent w) 1 : Sym.AlphabetSeries K) := by
  induction m with
  | zero =>
    intro n
    match n with
    | 0 =>
      rw [CreationSeeds.elemSymm_zero, map_one, map_one, Sym.boundedWords_zero_eq_univ,
        Finset.univ_unique, Finset.sum_singleton, Sym.wordExponent_of_length_zero]
      simp
    | p + 1 =>
      rw [Sym.boundedWords_zero_letters, Finset.sum_empty]
      refine map_elemSymm_eq_zero ((Sym.letterTrunc K 0).comp ι) (fun k hk => ?_) p.succ_pos
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [AlgHom.comp_apply, Sym.letterTrunc_realisation_powerSum hι, Finset.range_zero,
        Finset.sum_empty]
  | succ m ih =>
    intro n
    match n with
    | 0 =>
      rw [CreationSeeds.elemSymm_zero, map_one, map_one, Sym.boundedWords_zero_eq_univ,
        Finset.univ_unique, Finset.sum_singleton, Sym.wordExponent_of_length_zero]
      simp
    | p + 1 =>
      rw [Sym.sum_monomial_boundedWords_succ, ← ih (p + 1), ← ih p]
      have hstep := CreationSeeds.elemSymm_add_letter
        ((Sym.letterTrunc K m).comp ι : Sym.Lambda K →ₐ[K] Sym.AlphabetSeries K)
        ((Sym.letterTrunc K (m + 1)).comp ι : Sym.Lambda K →ₐ[K] Sym.AlphabetSeries K)
        (MvPowerSeries.X m : Sym.AlphabetSeries K)
        (fun k hk => by
          rw [AlgHom.comp_apply, AlgHom.comp_apply,
            Sym.letterTrunc_realisation_powerSum_succ hι m hk])
        (show 0 < p + 1 by omega)
      rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, Nat.add_sub_cancel] at hstep
      rw [hstep]

/-- **An elementary symmetric function is the fundamental of the full descent
set.** `ι(e_r) = F_{r,\{1,…,r-1\}}` for every realisation `ι` and every `r ≥ 1`.

Truncating to the first `m` letters turns the left side into a sum over the strictly increasing
words in those letters and the right side into the same sum, for every `m`; truncations separate
the alphabet series, so the two are equal. The usual hypothesis `r ≥ 1` is not
needed: at `r = 0` both sides are `1`, the empty word being the only word of length `0`. -/
@[hjo "lem_om_esymm_gessel"]
theorem realisation_elemSymm {K : Type*} [CommRing K] [Algebra ℚ K]
    {ι : Sym.Lambda K →ₐ[K] Sym.AlphabetSeries K} (hι : Sym.IsRealisation ι) (r : ℕ) :
    ι (Sym.elemSymm K r) = gessel K r (Ico 1 r) := by
  refine Sym.ext_letterTrunc.2 fun m => ?_
  rw [letterTrunc_realisation_elemSymm hι m r, letterTrunc_gessel K Subset.rfl m]

end HJO.ParkingFunctions
