/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import HJO.Symmetric.SymmetricFunctions
public meta import HJO.Attr

/-! # The objects behind sign extraction reading the full-descent coefficient

Sign extraction is read off a fundamental quasisymmetric expansion by polynomiality in the number
of letters, and this file carries the six objects that route needs: the evaluation `E_m` of a
power series in the alphabet at `m` letters each equal to `1`, the letter-count polynomial `ν_f`
of a symmetric function, the descent polynomial `D_{n,j}` counting weakly increasing words with
prescribed strict steps, and the words themselves -- the `S`-ascending words of length `n`, those
of them whose letters are among the first `m`, and the exponent vector of a word.

Two conventions are worth naming before they are used.

*The alphabet is indexed from `0`.* The ambient `Sym.AlphabetSeries K` is `K⟦x₀, x₁, …⟧`, so the
letters `x_1, …, x_m` of the usual `1`-based numbering are `x_0, …, x_{m-1}` here. The `1`-based
lower bound `1 ≤ i_1` on a word is therefore the vacuous `0 ≤ i_1`, and the bound `i_n ≤ m` on a
bounded word is `i_n < m`: both say that the word uses only the first `m` letters. This is the
reindexing already built into `ParkingFunctions.gessel`, whose tuples carry no lower bound either,
and it leaves every count unchanged -- what is counted is the words available in an alphabet of
`m` letters.

*A word of length `n` is a tuple, hence `Fin n → ℕ`, with `w k` standing for `i_{k+1}`.* The
positions are `0`-based while the descent set `S` stays `1`-based, as it is in
`ParkingFunctions.ides`: a step `j ∈ S`, which in the `1`-based numbering is the step from `i_j` to
`i_{j+1}`, is the step into the `0`-based position `j` from the `0`-based position `j - 1`.
Recording a word as a tuple rather than as a function `ℕ → ℕ` read on a window is what makes the
bounded words a `Finset`, so that their number -- the quantity the descent polynomial computes -- is
the cardinality of a finite set.
-/

@[expose] public section

open Finset
open scoped Nat

namespace HJO.Sym

/-! ### Evaluation at `m` letters -/

/-- Evaluation at `m` letters, `E_m`: the map sending a power series `G` in the alphabet to the
series in `y` whose coefficient of `y ^ N` is the sum of the coefficients of `G` at the exponent
vectors of total degree `N` supported in the first `m` letters. It is the evaluation at an
alphabet of `m` letters each equal to `1`: substituting `1` for `x_0, …, x_{m-1}` and `0` for the
remaining letters collapses the monomials of a fixed total degree `N` into the single term `y ^ N`.

The index set is finite for every `m` and `N`, so no convergence question arises and the
definition needs no auxiliary fact. -/
@[hjo "def_letter_eval"]
noncomputable def letterEval {K : Type*} [CommRing K] (m : ℕ) (G : AlphabetSeries K) :
    PowerSeries K :=
  PowerSeries.mk fun N => ∑ d ∈ (range m).finsuppAntidiag N, MvPowerSeries.coeff d G

/-- **The defining coefficients of the evaluation at `m` letters**: `[y^N] E_m(G)` is the sum of
`[x^d] G` over the exponent vectors `d` of total degree `N` supported in the first `m` letters,
which is the sum over the `m`-tuples `d_0 + ⋯ + d_{m-1} = N`. -/
@[hjo "def_letter_eval"]
theorem coeff_letterEval {K : Type*} [CommRing K] (m N : ℕ) (G : AlphabetSeries K) :
    PowerSeries.coeff N (letterEval m G) =
      ∑ d ∈ (range m).finsuppAntidiag N, MvPowerSeries.coeff d G :=
  PowerSeries.coeff_mk N _

/-! ### The letter-count polynomial -/

/-- The letter-count homomorphism `f ↦ ν_f`: the `K`-algebra homomorphism from `Lambda K` to
`K[t]` sending every formal power sum `p_k` to `t`. Since `Lambda K` is the polynomial algebra on
the `p_k`, prescribing those images determines it, and `MvPolynomial.aeval` is that prescription.

The value `ν_f(m)` at a non-negative integer `m` is the value of `f` at an alphabet of `m` letters
each equal to `1`, every power sum then counting the letters. Taking the polynomial rather than
that family of values is what allows `t = -1` to be substituted, which is where sign extraction
comes from. -/
@[hjo "def_letter_count_poly"]
noncomputable def letterCount (K : Type*) [CommRing K] : Lambda K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval fun _ => Polynomial.X

/-- The letter-count polynomial of the generator `i` of `Lambda K`, which stands for `p_{i+1}`. -/
@[simp]
theorem letterCount_X (K : Type*) [CommRing K] (i : ℕ) :
    letterCount K (MvPolynomial.X i) = Polynomial.X :=
  MvPolynomial.aeval_X _ i

/-- **The defining property of the letter-count polynomial**: `ν_{p_k} = t`. The natural
subtraction in `Sym.powerSum` makes `powerSum K 0` the same generator as `powerSum K 1`, so no
positivity hypothesis on `k` is needed. -/
@[hjo "def_letter_count_poly"]
theorem letterCount_powerSum (K : Type*) [CommRing K] (k : ℕ) :
    letterCount K (powerSum K k) = Polynomial.X :=
  letterCount_X K (k - 1)

/-! ### The descent polynomial -/

/-- The descent polynomial `D_{n,j} = (1 / n!) ∏_{r < n} (t - j + r) ∈ K[t]`, the reciprocal of
`n!` being taken in `K` through its `ℚ`-algebra structure.

At a non-negative integer `m` its value is the number of weakly increasing words of length `n` in
`m` letters with `j` prescribed strict steps; taking a polynomial in `t` rather than that family
of integers is again what allows `t = -1` to be substituted. -/
@[hjo "def_descent_poly"]
noncomputable def descentPoly (K : Type*) [CommRing K] [Algebra ℚ K] (n j : ℕ) :
    Polynomial K :=
  Polynomial.C (algebraMap ℚ K ((n ! : ℚ)⁻¹)) *
    ∏ r ∈ range n, (Polynomial.X - Polynomial.C ((j : K) - r))

section DescentPoly

variable (K : Type*) [CommRing K] [Algebra ℚ K]

/-- The descent polynomial with its denominator cleared: `n! · D_{n,j} = ∏_{r < n} (t - j + r)`,
the shape in which its values are computed. -/
theorem factorial_mul_descentPoly (n j : ℕ) :
    (n ! : Polynomial K) * descentPoly K n j =
      ∏ r ∈ range n, (Polynomial.X - Polynomial.C ((j : K) - r)) := by
  have h : (n ! : K) * algebraMap ℚ K ((n ! : ℚ)⁻¹) = 1 := by
    rw [← map_natCast (algebraMap ℚ K) (n !), ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), map_one]
  rw [descentPoly, ← mul_assoc, ← Polynomial.C_eq_natCast, ← Polynomial.C_mul, h, Polynomial.C_1,
    one_mul]

/-- The value of the descent polynomial at `x`, in the form `(1/n!) ∏_{r < n} (x - j + r)`. -/
theorem eval_descentPoly (n j : ℕ) (x : K) :
    (descentPoly K n j).eval x =
      algebraMap ℚ K ((n ! : ℚ)⁻¹) * ∏ r ∈ range n, (x - j + r) := by
  have hfactor : ∀ r ∈ range n,
      (Polynomial.X - Polynomial.C ((j : K) - r)).eval x = x - j + r := by
    intro r _
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    ring
  rw [descentPoly, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
    prod_congr rfl hfactor]

end DescentPoly

/-! ### The ascending words and their exponent vectors -/

/-- The tuple `w = (i_1, …, i_n)`, recorded as `w : Fin n → ℕ` with `w k` standing for `i_{k+1}`,
is an `S`-ascending word: it is weakly increasing, and it increases strictly at every step in `S`.
The tuples with this property form the set `W_{n,S}`.

The letters being indexed from `0`, the `1`-based lower bound `1 ≤ i_1` is vacuous here. Only the
elements of `S` in `[1, n-1]` constrain a word, that being the range in which the descent sets
used in this library live; on other values of `S` the condition is a totalization with no
mathematical content. That is `isAscendingWord_inter_Ico_iff`, and
`IsAscendingWord.mono_of_inter_subset` is the one-sided form it comes from. -/
@[hjo "def_ascending_word"]
structure IsAscendingWord (n : ℕ) (S : Finset ℕ) (w : Fin n → ℕ) : Prop where
  /-- An ascending word is weakly increasing: `i_1 ≤ i_2 ≤ ⋯ ≤ i_n`. -/
  monotone : Monotone w
  /-- An ascending word increases strictly at every step in `S`: `i_j < i_{j+1}` for `j ∈ S`,
  the `1`-based step `j` being the step into the `0`-based position `l = j`, taken from the
  `0`-based position `k` before it. -/
  lt_of_mem : ∀ k l : Fin n, (k : ℕ) + 1 = (l : ℕ) → (l : ℕ) ∈ S → w k < w l

/-- Being an `S`-ascending word is decidable: both conditions are bounded quantifications over
the finitely many positions. -/
instance instDecidableIsAscendingWord (n : ℕ) (S : Finset ℕ) (w : Fin n → ℕ) :
    Decidable (IsAscendingWord n S w) :=
  decidable_of_iff ((∀ k l : Fin n, k ≤ l → w k ≤ w l) ∧
      ∀ k l : Fin n, (k : ℕ) + 1 = (l : ℕ) → (l : ℕ) ∈ S → w k < w l)
    ⟨fun h => ⟨fun _ _ hkl => h.1 _ _ hkl, h.2⟩, fun h => ⟨fun _ _ hkl => h.1 hkl, h.2⟩⟩

/-- **Being ascending depends on the step set only inside the window**: a `T`-ascending word of
length `n` is `S`-ascending as soon as every step of `S` in `{1, …, n-1}` is a step of `T`. A
strict step is demanded only across a pair of adjacent positions of `Fin n`, and such a pair
exists exactly for a step in that window, so steps outside it are inert. -/
theorem IsAscendingWord.mono_of_inter_subset {n : ℕ} {S T : Finset ℕ} {w : Fin n → ℕ}
    (hw : IsAscendingWord n T w) (hST : S ∩ Ico 1 n ⊆ T) : IsAscendingWord n S w :=
  ⟨hw.monotone, fun k l hkl hmem =>
    hw.lt_of_mem k l hkl (hST (mem_inter.mpr ⟨hmem, mem_Ico.mpr ⟨by omega, l.2⟩⟩))⟩

/-- Being an `S`-ascending word is a property of `S ∩ Finset.Ico 1 n`: the totalization outside
the window `{1, …, n-1}` carries no content. -/
theorem isAscendingWord_inter_Ico_iff {n : ℕ} {S : Finset ℕ} {w : Fin n → ℕ} :
    IsAscendingWord n (S ∩ Ico 1 n) w ↔ IsAscendingWord n S w :=
  ⟨fun h => h.mono_of_inter_subset Subset.rfl,
    fun h => h.mono_of_inter_subset (inter_subset_left.trans inter_subset_left)⟩

/-- `W^{(m)}_{n,S}`, the `S`-ascending words of length `n` all of whose letters are among the
first `m`: since the letters are indexed from `0`, that is the `1`-based bound `i_n ≤ m` on the
last entry, in the form `i_n < m`. Bounding the letters makes these words a `Finset`, whose
cardinality is the count the descent polynomial computes. -/
@[hjo "def_bounded_word"]
def boundedWords (n : ℕ) (S : Finset ℕ) (m : ℕ) : Finset (Fin n → ℕ) :=
  {w ∈ Fintype.piFinset fun _ => range m | IsAscendingWord n S w}

/-- **Membership in the bounded words**: an `S`-ascending word of length `n` every letter of which
is among the first `m`. -/
@[hjo "def_bounded_word"]
theorem mem_boundedWords {n : ℕ} {S : Finset ℕ} {m : ℕ} {w : Fin n → ℕ} :
    w ∈ boundedWords n S m ↔ IsAscendingWord n S w ∧ ∀ k, w k < m := by
  rw [boundedWords, mem_filter, Fintype.mem_piFinset]
  simp only [mem_range]
  exact and_comm

/-- The bound on a bounded word is carried by its last entry alone, which is the form in which it
is usually stated: the entries are weakly increasing, so `i_n < m` bounds them all. -/
theorem mem_boundedWords_succ {n : ℕ} {S : Finset ℕ} {m : ℕ} {w : Fin (n + 1) → ℕ} :
    w ∈ boundedWords (n + 1) S m ↔ IsAscendingWord (n + 1) S w ∧ w (Fin.last n) < m := by
  rw [mem_boundedWords]
  exact ⟨fun h => ⟨h.1, h.2 _⟩,
    fun h => ⟨h.1, fun k => lt_of_le_of_lt (h.1.monotone (Fin.le_last k)) h.2⟩⟩

/-- The exponent vector `𝐝(w)` of a tuple `w = (i_1, …, i_n)`: the vector whose entry at the
letter `i` counts the positions carrying that letter, so that `x ^ 𝐝(w) = x_{i_1} ⋯ x_{i_n}` --
the form in which the monomials of `ParkingFunctions.gessel` are written. It is defined for an
arbitrary tuple: neither the ascending condition nor a descent set plays any role. -/
@[hjo "def_word_exponent"]
noncomputable def wordExponent {n : ℕ} (w : Fin n → ℕ) : ℕ →₀ ℕ := ∑ k, Finsupp.single (w k) 1

section WordExponent

variable {n : ℕ} (w : Fin n → ℕ)

/-- **The defining entries of the exponent vector of a word**: the entry at the letter `i` is the
number of positions `j` with `i_j = i`. -/
@[hjo "def_word_exponent"]
theorem wordExponent_apply (i : ℕ) : wordExponent w i = #{k | w k = i} := by
  rw [wordExponent, Finset.sum_apply', card_eq_sum_ones, sum_filter]
  exact sum_congr rfl fun k _ => Finsupp.single_apply

/-- The exponent vector of a word is supported on the letters the word uses. -/
theorem mem_support_wordExponent (i : ℕ) :
    i ∈ (wordExponent w).support ↔ ∃ k, w k = i := by
  rw [Finsupp.mem_support_iff, wordExponent_apply, card_ne_zero, filter_nonempty_iff]
  simp

/-- The exponent vector of a word of length `n` has total degree `n`, the degree being read on any
finite set of letters that contains the letters the word uses. -/
theorem sum_wordExponent {s : Finset ℕ} (hw : ∀ k, w k ∈ s) :
    ∑ i ∈ s, wordExponent w i = n := by
  have hcount : ∑ i ∈ s, wordExponent w i = ∑ i ∈ s, #{k | w k = i} :=
    sum_congr rfl fun i _ => wordExponent_apply w i
  have hmaps : Set.MapsTo w ((univ : Finset (Fin n)) : Set (Fin n)) (s : Set ℕ) :=
    fun k _ => mem_coe.mpr (hw k)
  rw [hcount, ← card_eq_sum_card_fiberwise hmaps, card_univ, Fintype.card_fin]

/-- The exponent vector of a word of length `n` in the first `m` letters is one of the exponent
vectors of total degree `n` that `letterEval m` sums over. -/
theorem wordExponent_mem_finsuppAntidiag {m : ℕ} (hw : ∀ k, w k < m) :
    wordExponent w ∈ (range m).finsuppAntidiag n := by
  refine mem_finsuppAntidiag.mpr ⟨sum_wordExponent w fun k => mem_range.mpr (hw k), ?_⟩
  intro i hi
  obtain ⟨k, hk⟩ := (mem_support_wordExponent w i).mp hi
  rw [mem_range, ← hk]
  exact hw k

end WordExponent

end HJO.Sym
