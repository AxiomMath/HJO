/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Intervals
public import HJO.Paths.Defs
public import HJO.SignExtraction.LetterEval
public import HJO.SignExtraction.Words
public meta import HJO.Attr

/-! # Sign extraction reads the full-descent coefficient: the fundamental functions

The coefficients of Gessel's fundamental quasisymmetric function `F_{n,S}` are read here off the
`S`-ascending words: the index set of `HJO.ParkingFunctions.gessel` is exactly the set of exponent
vectors of `S`-ascending words of length `n`, so a coefficient is `1` at such an exponent vector
and `0` at every other. Evaluating at `m` letters and taking the coefficient of `y^n` therefore
counts the `S`-ascending words in `m` letters, which is the value of the descent polynomial
`D_{n, #S}` at `m`.

The hypothesis `S ⊆ Ico 1 n` is needed and not cosmetic. `gessel` is total in `S`, and for `S`
outside that range its condition constrains the auxiliary sequence beyond the window a word of
length `n` occupies -- at `0 ∈ S` it would demand a letter strictly below the first one, which the
letters being indexed from `0` makes impossible. On the descent sets used in this library, which
are subsets of `{1, …, n-1}`, no such constraint arises and the two descriptions agree.
-/

@[expose] public section

open Finset

namespace HJO.ParkingFunctions

/-! ### The coefficients of a fundamental function -/

/-- The index set of `gessel` is hit: a coefficient of `F_{n,S}` at an exponent vector carried by
an admissible sequence is `1`. -/
theorem coeff_gessel_eq_one (K : Type*) [CommRing K] {n : ℕ} {S : Finset ℕ} {d : ℕ →₀ ℕ}
    (h : ∃ i : ℕ → ℕ, (∀ j ∈ Ico 1 n, i j ≤ i (j + 1)) ∧ (∀ j ∈ S, i j < i (j + 1)) ∧
      d = ∑ j ∈ Icc 1 n, Finsupp.single (i j) 1) :
    MvPowerSeries.coeff d (gessel K n S) = 1 := by
  rw [MvPowerSeries.coeff_apply, gessel]
  exact Set.indicator_of_mem h 1

/-- The index set of `gessel` is missed: a coefficient of `F_{n,S}` at an exponent vector carried
by no admissible sequence is `0`. -/
theorem coeff_gessel_eq_zero (K : Type*) [CommRing K] {n : ℕ} {S : Finset ℕ} {d : ℕ →₀ ℕ}
    (h : ¬ ∃ i : ℕ → ℕ, (∀ j ∈ Ico 1 n, i j ≤ i (j + 1)) ∧ (∀ j ∈ S, i j < i (j + 1)) ∧
      d = ∑ j ∈ Icc 1 n, Finsupp.single (i j) 1) :
    MvPowerSeries.coeff d (gessel K n S) = 0 := by
  rw [MvPowerSeries.coeff_apply, gessel]
  exact Set.indicator_of_notMem h 1

/-- A sum over the `1`-based positions `1, …, n` is a sum over the `0`-based positions of a
tuple of length `n`. -/
theorem sum_Icc_one_eq_sum_fin {M : Type*} [AddCommMonoid M] (g : ℕ → M) : ∀ n : ℕ,
    ∑ j ∈ Icc 1 n, g j = ∑ k : Fin n, g ((k : ℕ) + 1)
  | 0 => by simp
  | n + 1 => by
    rw [Fin.sum_univ_castSucc, sum_Icc_succ_top (by omega)]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [← sum_Icc_one_eq_sum_fin g n]

/-- A sum of unit vectors over the positions `1, …, n` is the exponent vector of the tuple the
summand reads. -/
theorem sum_Icc_single_eq_wordExponent (n : ℕ) (i : ℕ → ℕ) :
    ∑ j ∈ Icc 1 n, Finsupp.single (i j) 1
      = Sym.wordExponent (fun k : Fin n => i ((k : ℕ) + 1)) := by
  rw [Sym.wordExponent, sum_Icc_one_eq_sum_fin]

/-- Every `S`-ascending word carries an admissible sequence for `gessel`: reading the word on the
positions `1, …, n` and continuing by `0` outside them satisfies both conditions, the elements of
`S` all lying inside the window because `S ⊆ Ico 1 n`. -/
theorem exists_seq_of_isAscendingWord {n : ℕ} {S : Finset ℕ} (hS : S ⊆ Ico 1 n) {w : Fin n → ℕ}
    (hw : Sym.IsAscendingWord n S w) :
    ∃ i : ℕ → ℕ, (∀ j ∈ Ico 1 n, i j ≤ i (j + 1)) ∧ (∀ j ∈ S, i j < i (j + 1)) ∧
      Sym.wordExponent w = ∑ j ∈ Icc 1 n, Finsupp.single (i j) 1 := by
  have hval : ∀ (k : ℕ) (hk : k < n), (List.ofFn w).getD k 0 = w ⟨k, hk⟩ := by
    intro k hk
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_ofFn]
  refine ⟨fun j => (List.ofFn w).getD (j - 1) 0, ?_, ?_, ?_⟩
  · intro j hj
    rw [mem_Ico] at hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    change (List.ofFn w).getD (k + 1 - 1) 0 ≤ (List.ofFn w).getD (k + 1 + 1 - 1) 0
    rw [Nat.add_sub_cancel, Nat.add_sub_cancel, hval k (by omega), hval (k + 1) (by omega)]
    exact hw.monotone (Fin.mk_le_mk.mpr (by omega))
  · intro j hj
    have hj' := mem_Ico.mp (hS hj)
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    change (List.ofFn w).getD (k + 1 - 1) 0 < (List.ofFn w).getD (k + 1 + 1 - 1) 0
    rw [Nat.add_sub_cancel, Nat.add_sub_cancel, hval k (by omega), hval (k + 1) (by omega)]
    exact hw.lt_of_mem ⟨k, by omega⟩ ⟨k + 1, by omega⟩ rfl hj
  · have hfun : (fun k : Fin n => (List.ofFn w).getD ((k : ℕ) + 1 - 1) 0) = w := by
      funext k
      rw [Nat.add_sub_cancel, hval (k : ℕ) k.2]
    rw [sum_Icc_single_eq_wordExponent, hfun]

/-- Every admissible sequence for `gessel` carries an `S`-ascending word: reading the sequence on
the positions `1, …, n` gives a word with the same exponent vector. -/
theorem isAscendingWord_of_seq {n : ℕ} {S : Finset ℕ} {i : ℕ → ℕ}
    (h1 : ∀ j ∈ Ico 1 n, i j ≤ i (j + 1)) (h2 : ∀ j ∈ S, i j < i (j + 1)) :
    Sym.IsAscendingWord n S (fun k : Fin n => i ((k : ℕ) + 1)) ∧
      ∑ j ∈ Icc 1 n, Finsupp.single (i j) 1
        = Sym.wordExponent (fun k : Fin n => i ((k : ℕ) + 1)) := by
  refine ⟨⟨Sym.monotone_of_le_succ fun k l hkl => ?_, fun k l hkl hmem => ?_⟩,
    sum_Icc_single_eq_wordExponent n i⟩
  · have hl := l.2
    have hstep := h1 ((k : ℕ) + 1) (mem_Ico.mpr ⟨by omega, by omega⟩)
    change i ((k : ℕ) + 1) ≤ i ((l : ℕ) + 1)
    rw [show (l : ℕ) = (k : ℕ) + 1 from hkl.symm]
    exact hstep
  · have hstep := h2 ((k : ℕ) + 1) (by rw [hkl]; exact hmem)
    change i ((k : ℕ) + 1) < i ((l : ℕ) + 1)
    rw [show (l : ℕ) = (k : ℕ) + 1 from hkl.symm]
    exact hstep

/-- **The monomials of a fundamental occur once**: the coefficient of `F_{n,S}` at the exponent
vector of an `S`-ascending word is `1`. -/
@[hjo "lem_gessel_coeff_word"]
theorem coeff_wordExponent_gessel (K : Type*) [CommRing K] {n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Ico 1 n) {w : Fin n → ℕ} (hw : Sym.IsAscendingWord n S w) :
    MvPowerSeries.coeff (Sym.wordExponent w) (gessel K n S) = 1 :=
  coeff_gessel_eq_one K (exists_seq_of_isAscendingWord hS hw)

/-- **A fundamental has no other monomials**: the coefficient of `F_{n,S}` at an exponent vector
that is not the exponent vector of any `S`-ascending word is `0`. -/
@[hjo "lem_gessel_coeff_other"]
theorem coeff_gessel_eq_zero_of_forall_ne (K : Type*) [CommRing K] {n : ℕ} {S : Finset ℕ}
    {d : ℕ →₀ ℕ} (hd : ∀ w : Fin n → ℕ, Sym.IsAscendingWord n S w → d ≠ Sym.wordExponent w) :
    MvPowerSeries.coeff d (gessel K n S) = 0 := by
  refine coeff_gessel_eq_zero K ?_
  rintro ⟨i, h1, h2, rfl⟩
  obtain ⟨hasc, heq⟩ := isAscendingWord_of_seq h1 h2
  exact hd _ hasc heq

/-! ### The evaluation of a fundamental at `m` letters -/

/-- **The `m`-letter evaluation of a fundamental**: the coefficient of `y^{n+1}` in
`E_m(F_{n+1,S})` is the value of the descent polynomial `D_{n+1, #S}` at `m`. The exponent vectors
of total degree `n + 1` supported in the first `m` letters that contribute are exactly those of the
`S`-ascending words of length `n + 1` in those letters, each contributing `1`, so the coefficient
counts those words. -/
@[hjo "lem_gessel_letter_eval"]
theorem coeff_letterEval_gessel (K : Type*) [CommRing K] [Algebra ℚ K] {n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Ico 1 (n + 1)) (m : ℕ) :
    PowerSeries.coeff (n + 1) (Sym.letterEval m (gessel K (n + 1) S))
      = (Sym.descentPoly K (n + 1) #S).eval (m : K) := by
  classical
  have himg : ∀ w ∈ Sym.boundedWords (n + 1) S m,
      Sym.wordExponent w ∈ (range m).finsuppAntidiag (n + 1) := fun w hw =>
    Sym.wordExponent_mem_finsuppAntidiag w (Sym.mem_boundedWords.mp hw).2
  have hzero : ∀ d ∈ (range m).finsuppAntidiag (n + 1),
      d ∉ (Sym.boundedWords (n + 1) S m).image Sym.wordExponent →
        MvPowerSeries.coeff d (gessel K (n + 1) S) = 0 := by
    intro d hd hdnot
    refine coeff_gessel_eq_zero_of_forall_ne K fun w hw hdw => hdnot ?_
    have hlt : ∀ k, w k < m := by
      intro k
      refine mem_range.mp ((mem_finsuppAntidiag.mp hd).2 ?_)
      rw [hdw]
      exact (Sym.mem_support_wordExponent w (w k)).2 ⟨k, rfl⟩
    exact mem_image.mpr ⟨w, Sym.mem_boundedWords.mpr ⟨hw, hlt⟩, hdw.symm⟩
  have hinj : ∀ w ∈ Sym.boundedWords (n + 1) S m, ∀ w' ∈ Sym.boundedWords (n + 1) S m,
      Sym.wordExponent w = Sym.wordExponent w' → w = w' := fun w hw w' hw' h =>
    Sym.eq_of_wordExponent_eq (Sym.mem_boundedWords.mp hw).1 (Sym.mem_boundedWords.mp hw').1 h
  have hone : ∀ w ∈ Sym.boundedWords (n + 1) S m,
      MvPowerSeries.coeff (Sym.wordExponent w) (gessel K (n + 1) S) = 1 := fun w hw =>
    coeff_wordExponent_gessel K hS (Sym.mem_boundedWords.mp hw).1
  rw [Sym.coeff_letterEval, ← sum_subset (image_subset_iff.mpr himg) hzero, sum_image hinj,
    sum_congr rfl hone, sum_const, nsmul_eq_mul, mul_one,
    Sym.natCast_card_boundedWords K hS m]

end HJO.ParkingFunctions
