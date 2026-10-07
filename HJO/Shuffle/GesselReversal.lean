/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.LetterReversal
public import HJO.Shuffle.ShuffleAbove
public import HJO.SignExtraction.Basic
public meta import HJO.Attr

/-! # The Gessel reversal

Reflecting the degree-`n` window, `j ↦ n - j`, sends a fundamental quasisymmetric function
`F_{n,S}` to `F_{n,S^{∨n}}`, and that operation *fixes symmetric functions* — not the individual
fundamentals, only a symmetric combination of them. This file proves that, and with it
`HJO.GesselReverseSum`, one of the two hypotheses `HJO.shuffle_of_above` reduces the shuffle side of
the argument to. The other is `HJO.ShuffleAbove`, i.e. Mellit's Section 6.

The mechanism is the reversal `rv_m` of the first `m` letters of the alphabet
(`HJO.Sym.letterReverse`) together with the truncation `tr_m` (`HJO.Sym.letterTrunc`):

* `rv_m` and `tr_m` agree on a realised symmetric function
  (`HJO.Sym.letterReverse_realisation`, proved in `HJO.Shuffle.LetterReversal`), because a
  power sum is invariant under permuting its letters;
* `rv_m` carries `F_{n,S}` to `tr_m F_{n,S^{∨n}}` (`HJO.ParkingFunctions.letterReverse_gessel`),
  because reflecting a weakly increasing tuple in `{0,…,m-1}` reverses the positions of its strict
  steps;
* the family `(tr_m)_{m ≥ 0}` separates the points of `𝒫` (`HJO.Sym.ext_letterTrunc`).

Applying `rv_m` to a fundamental expansion of `ι f` therefore gives the reflected expansion after
`tr_m`, for every `m`, and the two expansions are then equal outright.

## Main results

* `HJO.ParkingFunctions.exists_tuple_blockRev`: the tuple bijection behind the reversal — reading a
  weakly increasing tuple backwards and reflecting its letters in the block of the first `m` turns
  the strict steps at `S` into strict steps at `S^{∨n}`.
* `HJO.ParkingFunctions.letterReverse_gessel`: `rv_m F_{n,S} = tr_m F_{n,S^{∨n}}`.
* `HJO.gessel_reverse_sum`: a fundamental expansion of a realised symmetric function stays an
  expansion of it after every descent set is reflected.
* `HJO.gesselReverseSum`: the same statement in the packaged form `HJO.GesselReverseSum L`, which is
  what `HJO.shuffle_of_above` consumes.

## Implementation notes

*The hypothesis `S ⊆ Finset.Ico 1 n` is not decoration.* `HJO.ParkingFunctions.gessel` is total in
`S`, but for `S` reaching outside the degree-`n` window the definition constrains the auxiliary
sequence beyond the tuple and is not a fundamental function of degree `n` — the counterexample
`gessel K 1 {1}` is the witness. The reversal is false there: with `j = n ∈ S` the tuple must have a
strict step from position `n` to position `n+1`, and position `n + 1` is not among the letters the
exponent vector records, so its value is unconstrained by the block and the reflection cannot be
inverted. Every statement here carries this containment.

*The `n ≥ 1` is not needed*, for `HJO.ParkingFunctions.letterReverse_gessel` or for
`HJO.gessel_reverse_sum`. At `n = 0` the containment `S ⊆ Finset.Ico 1 0` forces `S = ∅`, and both
sides are the constant `1` truncated, so the statement holds; no clause of either proof uses
positivity of `n`. This is a generalisation; the statements are otherwise the usual ones.

*The reflection used on exponent vectors is a permutation of the whole alphabet*,
`HJO.Sym.blockRevPerm m`, reflecting the first `m` letters and fixing the rest; see the
implementation notes of `HJO.Shuffle.LetterReversal` for why `rv_m` itself cannot be used in
the invariance argument.

## References

This file formalises the Gessel reversal, `HJO.ParkingFunctions.letterReverse_gessel` and
`HJO.gessel_reverse_sum`.
-/

@[expose] public section

open Finset

namespace HJO.ParkingFunctions

open HJO.Sym

/-- **The tuple bijection behind the reversal.** Let `e` be an exponent vector supported in the
first `m` letters which is the exponent vector of a weakly increasing tuple `i_1 ≤ … ≤ i_n` with a
strict step at every `j ∈ S`. Then the reflection of `e` in that block is the exponent vector of the
tuple `k ↦ m-1-i_{n+1-k}`, which is weakly increasing with a strict step at every
`k ∈ S^{∨n}` — the strict steps having been reversed along with the letters.

Applied twice, with `S^{∨n}` in place of `S`, this gives the converse, by
`HJO.ParkingFunctions.descentReverse_descentReverse`; that is how it is used below. -/
theorem exists_tuple_blockRev {m n : ℕ} {S : Finset ℕ} (hS : S ⊆ Ico 1 n) {e : ℕ →₀ ℕ}
    (he : ∀ j ∈ e.support, j < m)
    (h : ∃ i : ℕ → ℕ, (∀ j ∈ Ico 1 n, i j ≤ i (j + 1)) ∧ (∀ j ∈ S, i j < i (j + 1)) ∧
      e = ∑ j ∈ Icc 1 n, Finsupp.single (i j) 1) :
    ∃ i : ℕ → ℕ, (∀ j ∈ Ico 1 n, i j ≤ i (j + 1)) ∧
      (∀ j ∈ descentReverse n S, i j < i (j + 1)) ∧
      Finsupp.equivMapDomain (blockRevPerm m) e = ∑ j ∈ Icc 1 n, Finsupp.single (i j) 1 := by
  obtain ⟨i, h1, h2, rfl⟩ := h
  -- Every letter the tuple uses lies inside the block, because it occurs in the exponent vector.
  have hlt : ∀ j ∈ Icc 1 n, i j < m := by
    intro j hj
    refine he _ (Finsupp.mem_support_iff.2 ?_)
    rw [Finsupp.finsetSum_apply]
    have hle : 1 ≤ ∑ k ∈ Icc 1 n, (Finsupp.single (i k) (1 : ℕ)) (i j) := by
      have h0 := Finset.single_le_sum
        (f := fun k => (Finsupp.single (i k) (1 : ℕ)) (i j)) (fun _ _ => Nat.zero_le _) hj
      rwa [Finsupp.single_eq_same] at h0
    omega
  refine ⟨fun k => blockRev m (i (n + 1 - k)), fun k hk => ?_, fun k hk => ?_, ?_⟩
  · rw [mem_Ico] at hk
    change blockRev m (i (n + 1 - k)) ≤ blockRev m (i (n + 1 - (k + 1)))
    rw [show n + 1 - (k + 1) = n - k from by omega]
    refine blockRev_le_blockRev ?_ (hlt _ (by rw [mem_Icc]; omega))
    rw [show n + 1 - k = n - k + 1 from by omega]
    exact h1 _ (by rw [mem_Ico]; omega)
  · rw [mem_descentReverse] at hk
    obtain ⟨j, hjS, rfl⟩ := hk
    have hj := mem_Ico.1 (hS hjS)
    change blockRev m (i (n + 1 - (n - j))) < blockRev m (i (n + 1 - (n - j + 1)))
    rw [show n + 1 - (n - j) = j + 1 from by omega, show n + 1 - (n - j + 1) = j from by omega]
    exact blockRev_lt_blockRev (h2 j hjS) (hlt _ (by rw [mem_Icc]; omega))
  · rw [← Finsupp.domCongr_apply, map_sum]
    refine Finset.sum_nbij' (i := fun j => n + 1 - j) (j := fun k => n + 1 - k)
      (fun a ha => ?_) (fun a ha => ?_) (fun a ha => ?_) (fun a ha => ?_) (fun a ha => ?_)
    · rw [mem_Icc] at ha ⊢; omega
    · rw [mem_Icc] at ha ⊢; omega
    · rw [mem_Icc] at ha; omega
    · rw [mem_Icc] at ha; omega
    · have haa : n + 1 - (n + 1 - a) = a := by rw [mem_Icc] at ha; omega
      change (Finsupp.domCongr (blockRevPerm m)) (Finsupp.single (i a) 1)
        = Finsupp.single (blockRev m (i (n + 1 - (n + 1 - a)))) 1
      rw [haa, Finsupp.domCongr_apply, Finsupp.equivMapDomain_single, blockRevPerm_apply]

/-- **Reversal on a fundamental.** For every `S ⊆ {1,…,n-1}` and every `m`,
`rv_m(F_{n,S}) = tr_m(F_{n,S^{∨n}})`: the reversal kills every monomial using a letter outside the
first `m`, and on the rest it reads the weakly increasing tuples backwards with their letters
reflected, which reverses the positions of their strict steps. -/
@[hjo "lem_reversal_gessel"]
theorem letterReverse_gessel (K : Type*) [CommRing K] {n : ℕ} {S : Finset ℕ} (hS : S ⊆ Ico 1 n)
    (m : ℕ) :
    letterReverse K m (gessel K n S)
      = letterTrunc K m (gessel K n (descentReverse n S)) := by
  refine MvPowerSeries.ext fun d => ?_
  by_cases hd : ∀ j ∈ d.support, j < m
  · rw [coeff_letterReverse_of_support hd, coeff_letterTrunc_of_support hd]
    by_cases hmem : ∃ i : ℕ → ℕ, (∀ j ∈ Ico 1 n, i j ≤ i (j + 1)) ∧
        (∀ j ∈ S, i j < i (j + 1)) ∧
        Finsupp.equivMapDomain (blockRevPerm m) d = ∑ j ∈ Icc 1 n, Finsupp.single (i j) 1
    · rw [coeff_gessel_eq_one K hmem]
      refine (coeff_gessel_eq_one K ?_).symm
      have key := exists_tuple_blockRev hS (support_equivMapDomain_blockRevPerm hd) hmem
      rwa [equivMapDomain_blockRevPerm_involutive] at key
    · rw [coeff_gessel_eq_zero K hmem]
      refine (coeff_gessel_eq_zero K fun hcon => hmem ?_).symm
      have key := exists_tuple_blockRev (descentReverse_subset_Ico hS) hd hcon
      rwa [descentReverse_descentReverse (hS.trans Ico_subset_Iic_self)] at key
  · rw [coeff_letterReverse_of_not_support hd, coeff_letterTrunc_of_not_support hd]

end HJO.ParkingFunctions

namespace HJO

open ParkingFunctions

/-- **Complementing the descent sets of a symmetric expansion.** If a realisation `ι` sends `f` to a
combination of degree-`n` Gessel fundamentals whose descent sets lie in the window `{1,…,n-1}`, then
it also sends `f` to the combination with every descent set reflected. The individual fundamentals
are *not* fixed by the reflection; only the symmetric combination is.

Applying `rv_m` to the hypothesis turns it into a statement about `tr_m`, by
`HJO.Sym.letterReverse_realisation` on the left and `HJO.ParkingFunctions.letterReverse_gessel` on
the right; the two sides then agree after every truncation, and truncations separate
(`HJO.Sym.ext_letterTrunc`). -/
@[hjo "lem_gessel_reverse_sum"]
theorem gessel_reverse_sum {L : Type*} [Field L] [Algebra ℚ L]
    (ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L) (hι : Sym.IsRealisation ι) (n : ℕ) (I : Type)
    (s : Finset I) (w : I → L) (S : I → Finset ℕ) (hS : ∀ i ∈ s, S i ⊆ Ico 1 n)
    (f : Sym.Lambda L) (hf : ι f = ∑ i ∈ s, w i • gessel L n (S i)) :
    ι f = ∑ i ∈ s, w i • gessel L n (descentReverse n (S i)) := by
  refine Sym.ext_letterTrunc.2 fun m => ?_
  rw [← Sym.letterReverse_realisation hι f m, hf, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_smul, map_smul, letterReverse_gessel L (hS i hi) m]

/-- **The Gessel reversal, packaged.** `HJO.GesselReverseSum L` holds for every field `L` over `ℚ`:
this is the second of the two hypotheses of `HJO.shuffle_of_above`, so with it the whole shuffle
side of the argument rests on `HJO.ShuffleAbove` — Mellit's Section 6 — alone. -/
theorem gesselReverseSum (L : Type*) [Field L] [Algebra ℚ L] : GesselReverseSum L :=
  fun ι hι n I s w S hS f hf => gessel_reverse_sum ι hι n I s w S hS f hf

/-- **The below-diagonal shuffle identity from the above-diagonal one alone.** Since the Gessel
reversal is a theorem, `HJO.ShuffleNarrowed` follows from `HJO.ShuffleAbove` with nothing else
assumed. -/
theorem shuffleNarrowed_of_shuffleAbove {L : Type*} [Field L] [Algebra ℚ L]
    (h : ShuffleAbove L) : ShuffleNarrowed L :=
  shuffleNarrowed_of_above (gesselReverseSum L) h

/-- **The whole shuffle side of the argument, reduced to Mellit's Section 6.** The two-clause
assumption `HJO.External.Shuffle` follows from `HJO.ShuffleAbove` alone. -/
theorem shuffle_of_shuffleAbove {L : Type*} [Field L] [Algebra ℚ L] (h : ShuffleAbove L) :
    HJO.External.Shuffle L :=
  shuffle_of_above (gesselReverseSum L) h

end HJO
