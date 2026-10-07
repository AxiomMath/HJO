/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.Parameters
public import HJO.Classical.HsymmGessel
public import HJO.Classical.StdFibre
public import Mathlib.Data.Fintype.Perm
public meta import HJO.Attr

/-! # The fundamental expansion of a product over a composition

`HJO.ParkingFunctions.realisation_completeHomogComp` and
`HJO.ParkingFunctions.realisation_elemSymmComp`: for a realisation `ι` and a composition `α` of `n`,
both `ι(h_α)` and `ι(e_α)` expand over the *same* permutations of the positions, those whose descent
set lies in the partial-sum set `ps(α)` — the first with the inverse descent sets, the second with
them complemented.

## Main definitions

* `HJO.Sym.permDescentSet`: `Des(σ)` of a permutation of the positions.
* `HJO.Sym.blockWords`: the words in the first `m` letters comparing by a given relation across
  every step outside a step set `T`.

## Main statements

* `HJO.ParkingFunctions.realisation_completeHomogComp`.
* `HJO.ParkingFunctions.realisation_elemSymmComp`.

## Implementation notes

The two proofs are one proof run twice, with the relation `R` comparing adjacent letters weakly or
strictly and the standardisation replaced by the co-standardisation. Both halves are stated for a
general `R`, so the `h`-side and the `e`-side instantiate them rather than repeat them.

*Step one* is `HJO.Sym.prod_map_eq_sum_blockWords`, an induction on the list of parts: the truncated
realisation of `∏_i f(α_i)` is the sum of the monomials of the words of length `α.sum` in the first
`m` letters that compare by `R` across every step outside `ps(α)`. The induction step multiplies the
one-part formula by the inductive hypothesis and matches the product against the target by
concatenating the two words, `HJO.Sym.mem_blockWords_append` being the membership half of that
bijection. The arithmetic behind it is `HJO.Sym.compDescent`'s: no step below the first part lies in
`ps(a :: β)`, the step `a` itself lies in it as soon as the remaining parts have positive sum — so
no condition crosses the block boundary — and a step above `a` lies in it exactly when its shift by
`a` lies in `ps(β)`. The intermediate is stated with the raw length `α.sum` rather than with a
separate `n` and a hypothesis `α.sum = n`, which is what keeps the induction free of transport along
`Fin` equalities.

*Step two* is `HJO.Sym.sum_monomial_blockWords`, the grouping by the standardisation: the condition
cutting out those words depends on the word only through its standardisation
(`HJO.Sym.descentSet_std_subset_iff`, `HJO.Sym.descentSet_coStd_subset_iff`), so the sum splits over
the fibres, of which exactly the fibres of the permutations with `Des(σ) ⊆ ps(α)` contribute, each
summing to a truncated fundamental by `HJO.ParkingFunctions.sum_wordMonomial_stdPerm` and
`HJO.ParkingFunctions.sum_wordMonomial_coStdPerm`.

The two identities are honest equalities in `𝒫` between honest `Finset.sum`s, the index type
`Equiv.Perm (Fin n)` being finite; only the *proof* passes through the truncations, which is what
`HJO.Sym.ext_letterTrunc` is for.

*The usual hypothesis that the parts are positive is not needed*, and neither is `n ≥ 1`: a part
equal to `0` contributes `h_0 = e_0 = 1` and repeats a prefix sum, which changes neither side.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### The descent set of a permutation of the positions -/

/-- `Des(σ)` of a permutation of the positions: the descent set of the word `i ↦ σ(i)`, read through
`HJO.Sym.finWord`. It is the statistic the partial-sum set of a composition is compared against. -/
def permDescentSet {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset ℕ :=
  descentSet n (finWord fun i => ((σ i : Fin n) : ℕ))

section PermDescent

variable {α : Type*} [LinearOrder α] {n : ℕ}

/-- `Des` of the permutation `Std(u)` is `Des` of the tuple `Std(u)`. -/
theorem permDescentSet_stdPerm (u : Fin n → α) :
    permDescentSet (stdPerm u) = descentSet n (finWord (std u)) :=
  congrArg (fun f => descentSet n (finWord f)) (funext fun i => stdPerm_apply u i)

/-- `Des` of the permutation `Std⁻(u)` is `Des` of the tuple `Std⁻(u)`. -/
theorem permDescentSet_coStdPerm (u : Fin n → α) :
    permDescentSet (coStdPerm u) = descentSet n (finWord (coStd u)) :=
  congrArg (fun f => descentSet n (finWord f)) (funext fun i => coStdPerm_apply u i)

end PermDescent

/-! ### The blockwise words -/

/-- The words of length `n` in the first `m` letters that compare by `R` across every step outside
`T`: for `R = (· ≤ ·)` the words weakly increasing inside each block cut out by `T`, and for
`R = (· < ·)` the words strictly increasing inside each block. -/
def blockWords (R : ℕ → ℕ → Prop) [DecidableRel R] (n : ℕ) (T : Finset ℕ) (m : ℕ) :
    Finset (Fin n → ℕ) :=
  {u ∈ Fintype.piFinset fun _ : Fin n => range m |
    ∀ k l : Fin n, (k : ℕ) + 1 = (l : ℕ) → (l : ℕ) ∉ T → R (u k) (u l)}

section BlockWords

variable {R : ℕ → ℕ → Prop} [DecidableRel R] {n : ℕ} {T : Finset ℕ} {m : ℕ}

/-- **Membership in the blockwise words**: every letter is among the first `m`, and `R` holds across
every step outside `T`. -/
theorem mem_blockWords {u : Fin n → ℕ} :
    u ∈ blockWords R n T m ↔
      (∀ k, u k < m) ∧ ∀ k l : Fin n, (k : ℕ) + 1 = (l : ℕ) → (l : ℕ) ∉ T → R (u k) (u l) := by
  rw [blockWords, mem_filter, Fintype.mem_piFinset]
  simp only [mem_range]

/-- There is exactly one blockwise word of length zero, the empty tuple. -/
theorem blockWords_zero : blockWords R 0 T m = univ :=
  eq_univ_of_forall fun _u => mem_blockWords.2 ⟨fun k => k.elim0, fun k => k.elim0⟩

/-- **The weakly increasing bounded words are the blockwise words for `(· ≤ ·)` with no step
excluded**: with `T = ∅` the blockwise condition is weak increase at every step, which is
monotonicity, and that is what the empty descent set demands. -/
theorem boundedWords_empty_eq_blockWords (a m : ℕ) :
    boundedWords a ∅ m = blockWords (· ≤ ·) a ∅ m := by
  ext v
  rw [mem_boundedWords, mem_blockWords, isAscendingWord_empty_iff_monotone, and_comm]
  refine and_congr_right fun _ => ⟨fun h k l hkl _ => h (Fin.le_def.2 (by omega)),
    fun h => monotone_of_le_succ fun k l hkl => h k l hkl (notMem_empty _)⟩

/-- **The strictly increasing bounded words are the blockwise words for `(· < ·)` with no step
excluded**: with `T = ∅` the blockwise condition is strict increase at every step, which is what the
full descent set `\{1, …, a-1\}` demands. -/
theorem boundedWords_Ico_eq_blockWords (a m : ℕ) :
    boundedWords a (Ico 1 a) m = blockWords (· < ·) a ∅ m := by
  ext v
  rw [mem_boundedWords, mem_blockWords, and_comm]
  refine and_congr_right fun _ =>
    ⟨fun h k l hkl _ => h.lt_of_mem k l hkl (mem_Ico.2 ⟨by omega, l.isLt⟩), fun h => ?_⟩
  exact ⟨monotone_of_le_succ fun k l hkl => (h k l hkl (notMem_empty _)).le,
    fun k l hkl _ => h k l hkl (notMem_empty _)⟩

end BlockWords

/-! ### The partial-sum set of a composition with one part split off -/

/-- The proper prefix sums of `a :: β` are `a` plus those of `β`. -/
theorem sum_take_cons (a : ℕ) (β : List ℕ) (i : ℕ) :
    ((a :: β).take (i + 1)).sum = a + (β.take i).sum := by
  rw [List.take_succ_cons, List.sum_cons]

/-- **No step below the first part is a partial sum**: every element of `ps(a :: β)` is at least
`a`. -/
theorem notMem_compDescent_cons_of_lt {a j : ℕ} {β : List ℕ} (h : j < a) :
    j ∉ compDescent (a :: β) := by
  intro hmem
  obtain ⟨i, -, he⟩ := mem_compDescent.1 hmem
  rw [sum_take_cons] at he
  omega

/-- **The first part is itself a partial sum** as soon as the remaining parts have positive sum: the
prefix of length one has sum `a`, and there is a further part to make that prefix proper. -/
theorem mem_compDescent_cons_self {a : ℕ} {β : List ℕ} (h : 0 < β.sum) :
    a ∈ compDescent (a :: β) := by
  have hne : β ≠ [] := by
    intro hc
    rw [hc, List.sum_nil] at h
    omega
  refine mem_compDescent.2 ⟨0, ?_, ?_⟩
  · rw [List.length_cons, Nat.add_sub_cancel]
    exact List.length_pos_iff.2 hne
  · rw [sum_take_cons, List.take_zero, List.sum_nil, Nat.add_zero]

/-- **Above the first part, the partial sums of `a :: β` are those of `β` shifted by `a`.** -/
theorem mem_compDescent_cons_of_lt {a j : ℕ} {β : List ℕ} (h : a < j) :
    j ∈ compDescent (a :: β) ↔ j - a ∈ compDescent β := by
  rw [mem_compDescent, mem_compDescent, List.length_cons, Nat.add_sub_cancel]
  constructor
  · rintro ⟨i, hi, he⟩
    rw [sum_take_cons] at he
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := by
      match i with
      | 0 => rw [List.take_zero, List.sum_nil, Nat.add_zero] at he; omega
      | p + 1 => exact ⟨p, rfl⟩
    exact ⟨i', by omega, by omega⟩
  · rintro ⟨i, hi, he⟩
    refine ⟨i + 1, by omega, ?_⟩
    rw [sum_take_cons]
    omega

/-! ### Concatenating two blockwise words -/

section Append

variable {a s : ℕ} (v : Fin a → ℕ) (w : Fin s → ℕ)

/-- A concatenation read at a position of the first block. -/
theorem append_of_lt {x : Fin (a + s)} (h : (x : ℕ) < a) :
    Fin.append v w x = v ⟨(x : ℕ), h⟩ :=
  (congrArg (Fin.append v w) (Fin.ext (by simp) : x = Fin.castAdd s ⟨(x : ℕ), h⟩)).trans
    (Fin.append_left v w _)

/-- A concatenation read at a position of the second block. -/
theorem append_of_le {x : Fin (a + s)} (h : a ≤ (x : ℕ)) :
    Fin.append v w x = w ⟨(x : ℕ) - a, by have := x.isLt; omega⟩ :=
  (congrArg (Fin.append v w)
      (Fin.ext (by rw [Fin.val_natAdd]; exact (Nat.add_sub_cancel' h).symm) :
        x = Fin.natAdd a ⟨(x : ℕ) - a, by have := x.isLt; omega⟩)).trans
    (Fin.append_right v w _)

/-- **The exponent vector of a concatenation is the sum of the two exponent vectors**: the positions
of the concatenation split into those of the two halves. -/
theorem wordExponent_append : wordExponent (Fin.append v w) = wordExponent v + wordExponent w := by
  rw [wordExponent, wordExponent, wordExponent, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- **Cutting a tuple into its two blocks and reassembling it changes nothing.** -/
theorem append_castAdd_natAdd (u : Fin (a + s) → ℕ) :
    Fin.append (fun k => u (Fin.castAdd s k)) (fun k => u (Fin.natAdd a k)) = u := by
  funext x
  by_cases h : (x : ℕ) < a
  · rw [append_of_lt _ _ h]
    exact congrArg u (Fin.ext (by simp))
  · rw [append_of_le _ _ (by omega)]
    exact congrArg u (Fin.ext (by rw [Fin.val_natAdd]; exact Nat.add_sub_cancel' (by omega)))

end Append

/-- **A concatenation is blockwise exactly when both halves are.** Inside the first block no step of
`ps(a :: β)` occurs, so the condition there is the unconditional one; the step `a` across the block
boundary is a partial sum whenever it exists at all, so it imposes nothing; and a step inside the
second block is outside `ps(a :: β)` exactly when its shift is outside `ps(β)`. -/
theorem mem_blockWords_append {R : ℕ → ℕ → Prop} [DecidableRel R] {a : ℕ} {β : List ℕ} {m : ℕ}
    (v : Fin a → ℕ) (w : Fin β.sum → ℕ) :
    Fin.append v w ∈ blockWords R (a + β.sum) (compDescent (a :: β)) m ↔
      v ∈ blockWords R a ∅ m ∧ w ∈ blockWords R β.sum (compDescent β) m := by
  rw [mem_blockWords, mem_blockWords, mem_blockWords]
  constructor
  · rintro ⟨hb, hc⟩
    refine ⟨⟨fun k => ?_, fun k l hkl _ => ?_⟩, ⟨fun k => ?_, fun k l hkl hl => ?_⟩⟩
    · have h := hb (Fin.castAdd β.sum k)
      rwa [Fin.append_left] at h
    · have h := hc (Fin.castAdd β.sum k) (Fin.castAdd β.sum l) (by simpa using hkl)
        (by simpa using notMem_compDescent_cons_of_lt (β := β) l.isLt)
      rwa [Fin.append_left, Fin.append_left] at h
    · have h := hb (Fin.natAdd a k)
      rwa [Fin.append_right] at h
    · have hnot : ((Fin.natAdd a l : Fin (a + β.sum)) : ℕ) ∉ compDescent (a :: β) := by
        rw [Fin.val_natAdd, mem_compDescent_cons_of_lt (by omega : a < a + (l : ℕ))]
        simpa using hl
      have h := hc (Fin.natAdd a k) (Fin.natAdd a l)
        (by simp only [Fin.val_natAdd]; omega) hnot
      rwa [Fin.append_right, Fin.append_right] at h
  · rintro ⟨⟨hvb, hvc⟩, hwb, hwc⟩
    refine ⟨fun x => ?_, fun k l hkl hl => ?_⟩
    · by_cases h : (x : ℕ) < a
      · rw [append_of_lt _ _ h]
        exact hvb _
      · rw [append_of_le _ _ (by omega)]
        exact hwb _
    · rcases lt_trichotomy (l : ℕ) a with hl' | hl' | hl'
      · rw [append_of_lt _ _ (by omega : (k : ℕ) < a), append_of_lt _ _ hl']
        refine hvc _ _ ?_ (notMem_empty _)
        change (k : ℕ) + 1 = (l : ℕ)
        omega
      · refine absurd ?_ hl
        rw [hl']
        exact mem_compDescent_cons_self (a := a) (β := β) (by have := l.isLt; omega)
      · rw [append_of_le _ _ (by omega : a ≤ (k : ℕ)), append_of_le _ _ (le_of_lt hl')]
        refine hwc _ _ ?_ ?_
        · change (k : ℕ) - a + 1 = (l : ℕ) - a
          omega
        · change (l : ℕ) - a ∉ compDescent β
          rw [← mem_compDescent_cons_of_lt hl']
          exact hl

/-! ### Step one: the product over the parts counts the blockwise words -/

/-- **The truncated realisation of a product over a composition counts the blockwise words.** If a
ring homomorphism `φ` sends the one-part symmetric function `F a` to the sum of the monomials of the
blockwise words of length `a` with no step excluded, then it sends the product `∏_i F(α_i)` to the
sum of the monomials of the blockwise words of length `α.sum` with the steps of `ps(α)` excluded.

By induction on the list of parts. Splitting off the first part factors the product, and the two
sums multiply out into a sum over pairs of words, which `HJO.Sym.mem_blockWords_append` matches with
the sum over the concatenations. -/
theorem prod_map_eq_sum_blockWords {K : Type*} [CommRing K] {L : Type*} [CommRing L] {A : Type*}
    [FunLike A L (AlphabetSeries K)] [RingHomClass A L (AlphabetSeries K)] (φ : A)
    (R : ℕ → ℕ → Prop) [DecidableRel R] (F : ℕ → L) (m : ℕ)
    (hF : ∀ a : ℕ, φ (F a)
      = ∑ v ∈ blockWords R a ∅ m, (MvPowerSeries.monomial (wordExponent v) 1 : AlphabetSeries K))
    (α : List ℕ) :
    φ (α.map F).prod
      = ∑ u ∈ blockWords R α.sum (compDescent α) m,
          (MvPowerSeries.monomial (wordExponent u) 1 : AlphabetSeries K) := by
  induction α with
  | nil =>
    rw [List.map_nil, List.prod_nil, map_one, List.sum_nil, blockWords_zero, Finset.univ_unique,
      Finset.sum_singleton, wordExponent_of_length_zero]
    simp
  | cons a β ih =>
    rw [List.map_cons, List.prod_cons, map_mul, hF a, ih, List.sum_cons,
      Finset.sum_mul_sum (blockWords R a ∅ m) (blockWords R β.sum (compDescent β) m),
      ← Finset.sum_product' (blockWords R a ∅ m) (blockWords R β.sum (compDescent β) m)
        fun v w => (MvPowerSeries.monomial (wordExponent v) 1 : AlphabetSeries K)
          * MvPowerSeries.monomial (wordExponent w) 1]
    refine Finset.sum_nbij' (fun p => Fin.append p.1 p.2)
      (fun u => (fun k => u (Fin.castAdd β.sum k), fun k => u (Fin.natAdd a k)))
      (fun p hp => (mem_blockWords_append p.1 p.2).2 (Finset.mem_product.1 hp))
      (fun u hu => Finset.mem_product.2 ((mem_blockWords_append _ _).1
        (by rwa [append_castAdd_natAdd]))) (fun p _ => ?_) (fun u _ => ?_) fun p _ => ?_
    · exact Prod.ext (funext fun k => Fin.append_left p.1 p.2 k)
        (funext fun k => Fin.append_right p.1 p.2 k)
    · exact append_castAdd_natAdd u
    · rw [MvPowerSeries.monomial_mul_monomial, one_mul, wordExponent_append]

/-! ### Step two: grouping the blockwise words by their standardisation -/

/-- **The blockwise words group into standardisation fibres.** If a map `P` from words to
permutations has the property that `Des(P u) ⊆ T` is exactly the blockwise condition on `u`, and if
each fibre of `P` sums to a truncated series `tr_m(G σ)`, then the sum of the monomials of the
blockwise words is `∑_σ tr_m(G σ)` over the permutations with `Des(σ) ⊆ T`.

The first hypothesis makes the blockwise condition depend on the word only through `P u`, so the
fibres of the permutations with `Des(σ) ⊆ T` exhaust the blockwise words and no other fibre meets
them. -/
theorem sum_monomial_blockWords {K : Type*} [CommRing K] {n : ℕ} (R : ℕ → ℕ → Prop)
    [DecidableRel R] (P : (Fin n → ℕ) → Equiv.Perm (Fin n)) (G : Equiv.Perm (Fin n) →
      AlphabetSeries K) (T : Finset ℕ) (m : ℕ)
    (hP : ∀ u : Fin n → ℕ, permDescentSet (P u) ⊆ T ↔
      ∀ k l : Fin n, (k : ℕ) + 1 = (l : ℕ) → (l : ℕ) ∉ T → R (u k) (u l))
    (hfib : ∀ σ : Equiv.Perm (Fin n),
      ∑ u ∈ {u ∈ Fintype.piFinset fun _ : Fin n => range m | P u = σ},
          (MvPowerSeries.monomial (wordExponent u) 1 : AlphabetSeries K)
        = letterTrunc K m (G σ)) :
    ∑ u ∈ blockWords R n T m, (MvPowerSeries.monomial (wordExponent u) 1 : AlphabetSeries K)
      = ∑ σ ∈ {σ : Equiv.Perm (Fin n) | permDescentSet σ ⊆ T}, letterTrunc K m (G σ) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := P)
    (t := {σ : Equiv.Perm (Fin n) | permDescentSet σ ⊆ T})
    (fun u hu => mem_filter.2 ⟨mem_univ _, (hP u).2 (mem_blockWords.1 hu).2⟩)
    fun u => (MvPowerSeries.monomial (wordExponent u) 1 : AlphabetSeries K)]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  rw [← hfib σ]
  refine Finset.sum_congr (Finset.ext fun u => ?_) fun _ _ => rfl
  rw [mem_filter, mem_filter, blockWords, mem_filter]
  refine ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, ?_⟩, h.2⟩⟩
  exact (hP u).1 (h.2 ▸ (mem_filter.1 hσ).2)

end HJO.Sym

namespace HJO.ParkingFunctions

open HJO.Sym

/-- **The fundamental expansion of a complete homogeneous product.**
`ι(h_α) = ∑_σ F_{n,Des(σ⁻¹)}`, the sum over the permutations `σ` of the `n` positions with
`Des(σ) ⊆ ps(α)`.

Truncating to the first `m` letters, `HJO.Sym.prod_map_eq_sum_blockWords` turns the left side into
the sum of the monomials of the words weakly increasing inside each block cut out by `ps(α)`, and
`HJO.Sym.sum_monomial_blockWords` regroups that sum over the standardisation fibres; truncations
separate the alphabet series, so the two are equal. The usual hypotheses `n ≥ 1` and "the parts
of `α` are positive" are not used. -/
@[hjo "lem_om_hsymm_comp_gessel"]
theorem realisation_completeHomogComp {K : Type*} [CommRing K] [Algebra ℚ K]
    {ι : Sym.Lambda K →ₐ[K] Sym.AlphabetSeries K} (hι : Sym.IsRealisation ι)
    {n : ℕ} {α : List ℕ} (hα : α.sum = n) :
    ι (Sym.completeHomogComp K α)
      = ∑ σ ∈ {σ : Equiv.Perm (Fin n) | Sym.permDescentSet σ ⊆ Sym.compDescent α},
          gessel K n (Sym.invDescentSet σ) := by
  subst hα
  refine Sym.ext_letterTrunc.2 fun m => ?_
  rw [map_sum]
  have hstep : ((Sym.letterTrunc K m).comp ι) (Sym.completeHomogComp K α)
      = ∑ u ∈ blockWords (· ≤ ·) α.sum (compDescent α) m,
          (MvPowerSeries.monomial (wordExponent u) 1 : Sym.AlphabetSeries K) :=
    prod_map_eq_sum_blockWords ((Sym.letterTrunc K m).comp ι) (· ≤ ·) (Sym.completeHomog K) m
      (fun a => by
        rw [AlgHom.comp_apply, letterTrunc_realisation_completeHomog hι m a,
          boundedWords_empty_eq_blockWords]) α
  rw [AlgHom.comp_apply] at hstep
  rw [hstep]
  refine sum_monomial_blockWords (· ≤ ·) stdPerm (fun σ => gessel K α.sum (invDescentSet σ))
    (compDescent α) m (fun u => ?_) fun σ => ?_
  · rw [permDescentSet_stdPerm]
    exact descentSet_std_subset_iff _ u
  · rw [← sum_wordMonomial_stdPerm K σ m]
    exact Finset.sum_congr rfl fun u _ => (wordMonomial_eq_monomial u).symm

/-- **The fundamental expansion of an elementary symmetric product.**
`ι(e_α) = ∑_σ F_{n,\{1,…,n-1\}∖Des(σ⁻¹)}`, the sum over the *same* permutations `σ` as for `h_α`,
those with `Des(σ) ⊆ ps(α)`.

The proof of `HJO.ParkingFunctions.realisation_completeHomogComp` run with strict increase in place
of weak increase inside each block, and with the co-standardisation in place of the standardisation:
`HJO.Sym.descentSet_coStd_subset_iff` is the blockwise criterion and
`HJO.ParkingFunctions.sum_wordMonomial_coStdPerm` evaluates each fibre, at the complemented inverse
descent set. The usual hypotheses `n ≥ 1` and "the parts of `α` are positive" are not used. -/
@[hjo "lem_om_esymm_comp_gessel"]
theorem realisation_elemSymmComp {K : Type*} [CommRing K] [Algebra ℚ K]
    {ι : Sym.Lambda K →ₐ[K] Sym.AlphabetSeries K} (hι : Sym.IsRealisation ι)
    {n : ℕ} {α : List ℕ} (hα : α.sum = n) :
    ι (Sym.elemSymmComp K α)
      = ∑ σ ∈ {σ : Equiv.Perm (Fin n) | Sym.permDescentSet σ ⊆ Sym.compDescent α},
          gessel K n (Ico 1 n \ Sym.invDescentSet σ) := by
  subst hα
  refine Sym.ext_letterTrunc.2 fun m => ?_
  rw [map_sum]
  have hstep : ((Sym.letterTrunc K m).comp ι) (Sym.elemSymmComp K α)
      = ∑ u ∈ blockWords (· < ·) α.sum (compDescent α) m,
          (MvPowerSeries.monomial (wordExponent u) 1 : Sym.AlphabetSeries K) :=
    prod_map_eq_sum_blockWords ((Sym.letterTrunc K m).comp ι) (· < ·) (Sym.elemSymm K) m
      (fun a => by
        rw [AlgHom.comp_apply, letterTrunc_realisation_elemSymm hι m a,
          boundedWords_Ico_eq_blockWords]) α
  rw [AlgHom.comp_apply] at hstep
  rw [hstep]
  refine sum_monomial_blockWords (· < ·) coStdPerm
    (fun σ => gessel K α.sum (Ico 1 α.sum \ invDescentSet σ)) (compDescent α) m (fun u => ?_)
    fun σ => ?_
  · rw [permDescentSet_coStdPerm]
    exact descentSet_coStd_subset_iff _ u
  · rw [← sum_wordMonomial_coStdPerm K σ m]
    exact Finset.sum_congr rfl fun u _ => (wordMonomial_eq_monomial u).symm

end HJO.ParkingFunctions
