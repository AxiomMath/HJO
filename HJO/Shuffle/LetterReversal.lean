/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Rename
public import HJO.Symmetric.SymmetricFunctions
public meta import HJO.Attr

/-! # Truncating and reversing the letters of the alphabet

The alphabet lives in `𝒫 = K⟦x₀, x₁, …⟧` (`HJO.Sym.AlphabetSeries`). Two `K`-algebra
endomorphisms of `𝒫` are built here, both substitutions of variables by variables or by `0`:

* `HJO.Sym.letterTrunc K m` — `tr_m`, which fixes `x_i` for `i < m` and kills every later letter;
* `HJO.Sym.letterReverse K m` — `rv_m`, which sends `x_i` to `x_{m-1-i}` for `i < m` and kills
  every later letter.

The facts about them that the Gessel reversal needs are proved here: their coefficients, that the
family `(tr_m)_{m ≥ 0}` separates the points of `𝒫` (`HJO.Sym.ext_letterTrunc`), and that a
realised symmetric function is fixed by every renaming of the alphabet
(`HJO.Sym.letterPerm_realisation`), so that `rv_m` and `tr_m` agree on it
(`HJO.Sym.letterReverse_realisation`).

## Main definitions

* `HJO.Sym.letterTrunc K m`: `tr_m`, truncation to the first `m` letters.
* `HJO.Sym.letterReverse K m`: `rv_m`, reversal of the first `m` letters.
* `HJO.Sym.letterPerm K ρ`: renaming the alphabet along a permutation `ρ` of `ℕ`.
* `HJO.Sym.blockRev m`: the reflection `i ↦ m-1-i` of the first `m` letters, extended to `ℕ` by
  the identity — an involution of `ℕ`, hence a permutation `HJO.Sym.blockRevPerm m`.

## Main results

* `HJO.Sym.coeff_letterTrunc_of_support`, `HJO.Sym.coeff_letterTrunc_of_not_support`: `[x^d] tr_m G`
  is `[x^d] G` when `d` is supported in the first `m` letters, and `0` otherwise.
* `HJO.Sym.coeff_letterReverse_of_support`, `HJO.Sym.coeff_letterReverse_of_not_support`: likewise
  `[x^d] rv_m G` is the coefficient of `G` at `d` reflected by `blockRev m`, respectively `0`.
* `HJO.Sym.ext_letterTrunc`: `G = H ↔ ∀ m, tr_m G = tr_m H`.
* `HJO.Sym.letterPerm_realisation`: `ι f` is fixed by every renaming of the alphabet.
* `HJO.Sym.letterReverse_realisation`: `rv_m (ι f) = tr_m (ι f)`.

## Implementation notes

*The alphabet is indexed from `0`*, as everywhere here, so the letters `x_1, …, x_m` of the usual
`1`-indexed notation are `x₀, …, x_{m-1}` and its clauses `tr_m(x_i) = x_i` for `1 ≤ i ≤ m`,
`rv_m(x_i) = x_{m+1-i}` for `1 ≤ i ≤ m`, both `= 0` for `i > m`, read `i < m` and `m ≤ i` here,
with the reflection `i ↦ m-1-i`.

*The values on the letters are a consequence, not the definition.* On a power series ring the
images of the `x_i` do not pin an endomorphism: `𝒫` is not the free commutative `K`-algebra on the
`x_i`, and a series involving infinitely many letters lies outside the subalgebra they generate, so
with no continuity assumed the clauses on the letters constrain the map only on polynomials. What
is meant is the substitution acting monomial-wise, and that is what is defined here: both maps
are the composite of `MvPowerSeries.killCompl Fin.valEmbedding`, which reads off the coefficients
at the exponent vectors supported in the first `m` letters, with a `MvPowerSeries.rename` putting
them back — at the same vectors for `tr_m`, at the reflected ones for `rv_m`. Building them from
two algebra maps is what makes them `AlgHom`s with no proof obligation, and the clauses on the
letters are theorems about them rather than part of the definition.

*Why a permutation of the whole alphabet appears.* `rv_m` and `tr_m` agree on a realised symmetric
function because a power sum is invariant under permuting its letters. That invariance is an
equality of algebra homomorphisms out of `Lambda K`, so it is proved by `MvPolynomial.algHom_ext`
on the generators — but only for a renaming of `𝒫` along a *permutation of `ℕ`*, `letterPerm`,
since `rv_m` itself is not injective. So the reflection is carried out by `letterPerm` along
`blockRevPerm m`, which reflects the first `m` letters and fixes the rest, and the coefficient
lemmas relate `rv_m` to it.

*`blockRev m` is an involution of `ℕ` for every `m`*, including `m = 0`, where it is the identity:
inside the block, `m - 1 - (m - 1 - i) = i` because `i ≤ m - 1`, and outside it the map is the
identity, the block being mapped to itself so that the two clauses never cross.

## References

This file formalises the definitions `HJO.Sym.letterTrunc` and `HJO.Sym.letterReverse` and the
lemmas `HJO.Sym.ext_letterTrunc` and `HJO.Sym.letterReverse_realisation`, on reversing the letters
of a realisation.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### Two facts about reindexing exponent vectors -/

/-- Embedding along a permutation is reindexing along it. -/
theorem embDomain_toEmbedding {σ τ : Type*} (ρ : σ ≃ τ) (c : σ →₀ ℕ) :
    Finsupp.embDomain ρ.toEmbedding c = Finsupp.equivMapDomain ρ c := by
  rw [Finsupp.embDomain_eq_mapDomain, Finsupp.equivMapDomain_eq_mapDomain, Equiv.coe_toEmbedding]

/-- Reindexing along a permutation and along its inverse are mutually inverse. -/
theorem equivMapDomain_symm_self {σ τ : Type*} (ρ : σ ≃ τ) (d : τ →₀ ℕ) :
    Finsupp.equivMapDomain ρ (Finsupp.equivMapDomain ρ.symm d) = d := by
  rw [← Finsupp.equivMapDomain_trans, Equiv.symm_trans_self, Finsupp.equivMapDomain_refl]

/-! ### Renaming the alphabet along a permutation -/

/-- Renaming the alphabet along a permutation `ρ` of `ℕ`: the `K`-algebra endomorphism of `𝒫`
substituting `x_{ρ i}` for `x_i`. Unlike `letterTrunc` and `letterReverse` this loses nothing, and
it is the form in which the invariance of a realised symmetric function is provable — an equality
of algebra homomorphisms out of `Lambda K`. -/
noncomputable def letterPerm (K : Type*) [CommRing K] (ρ : ℕ ≃ ℕ) :
    AlphabetSeries K →ₐ[K] AlphabetSeries K :=
  MvPowerSeries.rename (ρ.toEmbedding : ℕ → ℕ)

/-- `[x^d] letterPerm K ρ G` is the coefficient of `G` at the exponent vector obtained from `d` by
reindexing along `ρ⁻¹`. -/
theorem coeff_letterPerm {K : Type*} [CommRing K] (ρ : ℕ ≃ ℕ) (G : AlphabetSeries K)
    (d : ℕ →₀ ℕ) :
    MvPowerSeries.coeff d (letterPerm K ρ G)
      = MvPowerSeries.coeff (Finsupp.equivMapDomain ρ.symm d) G := by
  have h : Finsupp.embDomain ρ.toEmbedding (Finsupp.equivMapDomain ρ.symm d) = d := by
    rw [embDomain_toEmbedding, equivMapDomain_symm_self]
  conv_lhs => rw [← h]
  exact MvPowerSeries.coeff_embDomain_rename _ _ _

/-! ### Truncation and reversal of the first letters -/

/-- `tr_m`, truncation of the alphabet to its first `m` letters: the `K`-algebra endomorphism of
`AlphabetSeries K = K⟦x₀, x₁, …⟧` substituting `x_i` for `x_i` when `i < m` and `0` for `x_i` when
`m ≤ i`. Equivalently it fixes every monomial in `x₀, …, x_{m-1}` and kills every monomial
involving a later letter, so that `[x^d] tr_m(G)` is `[x^d] G` when `d` is supported in the first
`m` letters and `0` otherwise. The alphabet being indexed from `0`, these are the letters
`x_1, …, x_m` of the `1`-indexed notation. -/
@[hjo "def_letter_truncation"]
noncomputable def letterTrunc (K : Type*) [CommRing K] (m : ℕ) :
    AlphabetSeries K →ₐ[K] AlphabetSeries K :=
  (MvPowerSeries.rename (Fin.valEmbedding (n := m))).comp
    (MvPowerSeries.killCompl (Fin.valEmbedding (n := m)))

/-- `rv_m`, reversal of the first `m` letters of the alphabet: the `K`-algebra endomorphism of
`AlphabetSeries K = K⟦x₀, x₁, …⟧` substituting `x_{m-1-i}` for `x_i` when `i < m` and `0` for
`x_i` when `m ≤ i`. Equivalently it sends a monomial in `x₀, …, x_{m-1}` to the monomial obtained
by reflecting that block of letters, and kills every monomial involving a later letter. The
alphabet being indexed from `0`, these are the letters `x_1, …, x_m` of the `1`-indexed notation
and its substitution `x_i ↦ x_{m+1-i}`. -/
@[hjo "def_letter_reversal"]
noncomputable def letterReverse (K : Type*) [CommRing K] (m : ℕ) :
    AlphabetSeries K →ₐ[K] AlphabetSeries K :=
  (MvPowerSeries.rename ((Fin.revPerm (n := m)).toEmbedding.trans Fin.valEmbedding)).comp
    (MvPowerSeries.killCompl (Fin.valEmbedding (n := m)))

theorem letterTrunc_apply (K : Type*) [CommRing K] (m : ℕ) (G : AlphabetSeries K) :
    letterTrunc K m G = MvPowerSeries.rename (Fin.valEmbedding (n := m) : Fin m → ℕ)
      (MvPowerSeries.killCompl (Fin.valEmbedding (n := m)) G) := rfl

theorem letterReverse_apply (K : Type*) [CommRing K] (m : ℕ) (G : AlphabetSeries K) :
    letterReverse K m G = MvPowerSeries.rename
        (((Fin.revPerm (n := m)).toEmbedding.trans Fin.valEmbedding : Fin m ↪ ℕ) : Fin m → ℕ)
      (MvPowerSeries.killCompl (Fin.valEmbedding (n := m)) G) := rfl

/-! ### The clauses on the letters

These four are the usual *definitions* of `tr_m` and `rv_m`, which as explained above do not
determine an endomorphism of `𝒫` and are therefore theorems about the substitutions built here. They
are also what makes the two definitions verifiably non-degenerate: `rv_2(x₀) = x₁` while
`tr_2(x₀) = x₀`, so neither map is zero, the identity, or the other. -/

/-- The first block of the alphabet is exactly the letters `x_i` with `i < m`. -/
theorem range_valEmbedding (m : ℕ) :
    Set.range (Fin.valEmbedding (n := m) : Fin m → ℕ) = {j : ℕ | j < m} := by
  ext j
  exact ⟨fun ⟨i, hi⟩ => hi ▸ i.isLt, fun hj => ⟨⟨j, hj⟩, rfl⟩⟩

/-- `tr_m(x_i) = x_i` for `i < m`. -/
theorem letterTrunc_X_of_lt {K : Type*} [CommRing K] {m i : ℕ} (h : i < m) :
    letterTrunc K m (MvPowerSeries.X i) = (MvPowerSeries.X i : AlphabetSeries K) := by
  have h1 : (MvPowerSeries.X i : AlphabetSeries K)
      = MvPowerSeries.X (Fin.valEmbedding (⟨i, h⟩ : Fin m)) := rfl
  rw [letterTrunc_apply, h1, MvPowerSeries.killCompl_X, MvPowerSeries.rename_X]

/-- `tr_m(x_i) = 0` for `m ≤ i`. -/
theorem letterTrunc_X_of_le {K : Type*} [CommRing K] {m i : ℕ} (h : m ≤ i) :
    letterTrunc K m (MvPowerSeries.X i) = (0 : AlphabetSeries K) := by
  rw [letterTrunc_apply, MvPowerSeries.killCompl_X_eq_zero
    (by rw [range_valEmbedding]; exact Nat.not_lt.2 h), map_zero]

/-- `rv_m(x_i) = x_{m-1-i}` for `i < m` — the `1`-indexed `rv_m(x_i) = x_{m+1-i}` for
`1 ≤ i ≤ m`, the alphabet being indexed from `0`. -/
theorem letterReverse_X_of_lt {K : Type*} [CommRing K] {m i : ℕ} (h : i < m) :
    letterReverse K m (MvPowerSeries.X i) = (MvPowerSeries.X (m - 1 - i) : AlphabetSeries K) := by
  have h1 : (MvPowerSeries.X i : AlphabetSeries K)
      = MvPowerSeries.X (Fin.valEmbedding (⟨i, h⟩ : Fin m)) := rfl
  rw [letterReverse_apply, h1, MvPowerSeries.killCompl_X, MvPowerSeries.rename_X]
  exact congrArg MvPowerSeries.X (by change m - (i + 1) = m - 1 - i; omega)

/-- `rv_m(x_i) = 0` for `m ≤ i`. -/
theorem letterReverse_X_of_le {K : Type*} [CommRing K] {m i : ℕ} (h : m ≤ i) :
    letterReverse K m (MvPowerSeries.X i) = (0 : AlphabetSeries K) := by
  rw [letterReverse_apply, MvPowerSeries.killCompl_X_eq_zero
    (by rw [range_valEmbedding]; exact Nat.not_lt.2 h), map_zero]

/-- An exponent vector supported in the first `m` letters is the image of one indexed by
`Fin m`. -/
theorem exists_embDomain_val {m : ℕ} {d : ℕ →₀ ℕ} (hd : ∀ i ∈ d.support, i < m) :
    ∃ c : Fin m →₀ ℕ, Finsupp.embDomain (Fin.valEmbedding (n := m)) c = d :=
  (Finsupp.mem_range_embDomain_iff _ d).2 fun j hj => by
    rw [range_valEmbedding]; exact hd j hj

/-- Conversely, an exponent vector *not* supported in the first `m` letters is outside the image of
`Finsupp.mapDomain` along any embedding of `Fin m`. -/
theorem not_mem_range_mapDomain {m : ℕ} {d : ℕ →₀ ℕ} (e : Fin m ↪ ℕ)
    (he : ∀ i : Fin m, e i < m) (hd : ¬ ∀ i ∈ d.support, i < m) :
    d ∉ Set.range (Finsupp.mapDomain (e : Fin m → ℕ)) := by
  intro hmem
  rw [show (Finsupp.mapDomain (e : Fin m → ℕ) : (Fin m →₀ ℕ) → (ℕ →₀ ℕ))
      = Finsupp.embDomain e from (funext (Finsupp.embDomain_eq_mapDomain e)).symm] at hmem
  exact hd fun j hj => by
    obtain ⟨i, hi⟩ := (Finsupp.mem_range_embDomain_iff e d).1 hmem hj
    exact hi ▸ he i

/-- **The coefficients of a truncation, inside the block.** -/
theorem coeff_letterTrunc_of_support {K : Type*} [CommRing K] {m : ℕ} {d : ℕ →₀ ℕ}
    (hd : ∀ i ∈ d.support, i < m) (G : AlphabetSeries K) :
    MvPowerSeries.coeff d (letterTrunc K m G) = MvPowerSeries.coeff d G := by
  obtain ⟨c, rfl⟩ := exists_embDomain_val hd
  rw [letterTrunc_apply, MvPowerSeries.coeff_embDomain_rename, MvPowerSeries.coeff_killCompl]

/-- **The coefficients of a truncation, outside the block.** -/
theorem coeff_letterTrunc_of_not_support {K : Type*} [CommRing K] {m : ℕ} {d : ℕ →₀ ℕ}
    (hd : ¬ ∀ i ∈ d.support, i < m) (G : AlphabetSeries K) :
    MvPowerSeries.coeff d (letterTrunc K m G) = 0 := by
  rw [letterTrunc_apply]
  apply MvPowerSeries.coeff_rename_eq_zero
  exact not_mem_range_mapDomain _ (fun i => i.isLt) hd

/-- **Truncations separate the alphabet series.** Two elements of `AlphabetSeries K` are equal
exactly when their truncations to the first `m` letters agree for every `m`: a monomial involves
only finitely many letters, so `tr_m` recovers its coefficient for all large `m`. The interesting
direction, `mpr`, is the substance of the lemma; the converse is `congrArg`. -/
@[hjo "lem_truncation_separates"]
theorem ext_letterTrunc {K : Type*} [CommRing K] {G H : AlphabetSeries K} :
    G = H ↔ ∀ m : ℕ, letterTrunc K m G = letterTrunc K m H := by
  refine ⟨fun h m => by rw [h], fun h => MvPowerSeries.ext fun d => ?_⟩
  have hd : ∀ i ∈ d.support, i < d.support.sup id + 1 := fun i hi =>
    Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  have key := congrArg (MvPowerSeries.coeff d) (h (d.support.sup id + 1))
  rwa [coeff_letterTrunc_of_support hd, coeff_letterTrunc_of_support hd] at key

/-! ### The reflection of the first block -/

/-- The reflection `i ↦ m-1-i` of the first `m` letters, extended to `ℕ` by the identity. -/
def blockRev (m i : ℕ) : ℕ := if i < m then m - 1 - i else i

theorem blockRev_of_lt {m i : ℕ} (h : i < m) : blockRev m i = m - 1 - i := by
  simp only [blockRev, h, ite_true]

theorem blockRev_of_le {m i : ℕ} (h : m ≤ i) : blockRev m i = i := by
  simp only [blockRev, Nat.not_lt.2 h, ite_false]

theorem blockRev_involutive (m : ℕ) : Function.Involutive (blockRev m) := fun i => by
  by_cases h : i < m
  · have h2 : m - 1 - i < m := by omega
    rw [blockRev_of_lt h, blockRev_of_lt h2]
    omega
  · have h1 : m ≤ i := by omega
    rw [blockRev_of_le h1, blockRev_of_le h1]

/-- The reflection maps the block to itself. -/
theorem blockRev_lt {m i : ℕ} (h : i < m) : blockRev m i < m := by
  rw [blockRev_of_lt h]; omega

/-- On the block the reflection is antitone. -/
theorem blockRev_le_blockRev {m a b : ℕ} (hab : a ≤ b) (hb : b < m) :
    blockRev m b ≤ blockRev m a := by
  rw [blockRev_of_lt hb, blockRev_of_lt (by omega : a < m)]; omega

/-- On the block the reflection is strictly antitone. -/
theorem blockRev_lt_blockRev {m a b : ℕ} (hab : a < b) (hb : b < m) :
    blockRev m b < blockRev m a := by
  rw [blockRev_of_lt hb, blockRev_of_lt (by omega : a < m)]; omega

/-- The reflection of the first `m` letters, as a permutation of the alphabet. -/
def blockRevPerm (m : ℕ) : ℕ ≃ ℕ := (blockRev_involutive m).toPerm _

@[simp] theorem blockRevPerm_apply (m i : ℕ) : blockRevPerm m i = blockRev m i := rfl

@[simp] theorem blockRevPerm_symm (m : ℕ) : (blockRevPerm m).symm = blockRevPerm m :=
  (blockRev_involutive m).toPerm_symm

/-- Reflecting the alphabet twice returns every exponent vector. -/
theorem equivMapDomain_blockRevPerm_involutive (m : ℕ) (d : ℕ →₀ ℕ) :
    Finsupp.equivMapDomain (blockRevPerm m) (Finsupp.equivMapDomain (blockRevPerm m) d) = d := by
  conv_rhs => rw [← equivMapDomain_symm_self (blockRevPerm m) d]
  rw [blockRevPerm_symm]

/-- Reflecting the alphabet preserves being supported in the first `m` letters. -/
theorem support_equivMapDomain_blockRevPerm {m : ℕ} {d : ℕ →₀ ℕ} (hd : ∀ i ∈ d.support, i < m) :
    ∀ i ∈ (Finsupp.equivMapDomain (blockRevPerm m) d).support, i < m := by
  intro i hi
  rw [Finsupp.mem_support_iff, Finsupp.equivMapDomain_apply, blockRevPerm_symm,
    blockRevPerm_apply] at hi
  have hlt : blockRev m i < m := hd _ (Finsupp.mem_support_iff.2 hi)
  by_cases h : i < m
  · exact h
  · rw [blockRev_of_le (Nat.not_lt.1 h)] at hlt; exact hlt

/-- On an exponent vector supported in the first `m` letters, reflecting the alphabet by
`blockRev m` is `Fin.rev` on the block. -/
theorem equivMapDomain_blockRevPerm_embDomain {m : ℕ} (c : Fin m →₀ ℕ) :
    Finsupp.equivMapDomain (blockRevPerm m) (Finsupp.embDomain (Fin.valEmbedding (n := m)) c)
      = Finsupp.embDomain (Fin.valEmbedding (n := m))
          (Finsupp.equivMapDomain (Fin.revPerm (n := m)).symm c) := by
  ext j
  rw [Finsupp.equivMapDomain_apply, blockRevPerm_symm, blockRevPerm_apply]
  by_cases hj : j < m
  · have key : ∀ i : Fin m,
        (Finsupp.embDomain (Fin.valEmbedding (n := m)) c) (blockRev m (i : ℕ))
          = (Finsupp.embDomain (Fin.valEmbedding (n := m))
              (Finsupp.equivMapDomain (Fin.revPerm (n := m)).symm c)) (i : ℕ) := by
      intro i
      have h1 : blockRev m (i : ℕ) = ((i.rev : Fin m) : ℕ) := by
        rw [blockRev_of_lt i.isLt, Fin.val_rev]; omega
      rw [h1]
      change (Finsupp.embDomain (Fin.valEmbedding (n := m)) c) (Fin.valEmbedding i.rev)
          = (Finsupp.embDomain (Fin.valEmbedding (n := m))
              (Finsupp.equivMapDomain (Fin.revPerm (n := m)).symm c)) (Fin.valEmbedding i)
      rw [Finsupp.embDomain_apply_self, Finsupp.embDomain_apply_self,
        Finsupp.equivMapDomain_apply, Equiv.symm_symm, Fin.revPerm_apply]
    exact key ⟨j, hj⟩
  · have hnot : j ∉ Set.range (Fin.valEmbedding (n := m) : Fin m → ℕ) := by
      rw [range_valEmbedding]; exact hj
    rw [blockRev_of_le (Nat.not_lt.1 hj), Finsupp.embDomain_of_notMem_range _ _ _ hnot,
      Finsupp.embDomain_of_notMem_range _ _ _ hnot]

/-! ### The coefficients of a reversal -/

/-- **The coefficients of a reversal, inside the block.** `[x^d] rv_m G` is the coefficient of `G`
at the exponent vector obtained from `d` by reflecting the first `m` letters. -/
theorem coeff_letterReverse_of_support {K : Type*} [CommRing K] {m : ℕ} {d : ℕ →₀ ℕ}
    (hd : ∀ i ∈ d.support, i < m) (G : AlphabetSeries K) :
    MvPowerSeries.coeff d (letterReverse K m G)
      = MvPowerSeries.coeff (Finsupp.equivMapDomain (blockRevPerm m) d) G := by
  obtain ⟨c, rfl⟩ := exists_embDomain_val hd
  rw [equivMapDomain_blockRevPerm_embDomain, letterReverse_apply]
  have key : Finsupp.embDomain
      ((Fin.revPerm (n := m)).toEmbedding.trans (Fin.valEmbedding (n := m)))
      (Finsupp.equivMapDomain (Fin.revPerm (n := m)).symm c)
      = Finsupp.embDomain (Fin.valEmbedding (n := m)) c := by
    rw [Finsupp.embDomain_trans_apply, embDomain_toEmbedding, equivMapDomain_symm_self]
  rw [← key, MvPowerSeries.coeff_embDomain_rename, MvPowerSeries.coeff_killCompl]

/-- **The coefficients of a reversal, outside the block.** -/
theorem coeff_letterReverse_of_not_support {K : Type*} [CommRing K] {m : ℕ} {d : ℕ →₀ ℕ}
    (hd : ¬ ∀ i ∈ d.support, i < m) (G : AlphabetSeries K) :
    MvPowerSeries.coeff d (letterReverse K m G) = 0 := by
  rw [letterReverse_apply]
  apply MvPowerSeries.coeff_rename_eq_zero
  exact not_mem_range_mapDomain _ (fun i => (Fin.revPerm i).isLt) hd

/-! ### Reversal fixes a realised symmetric function -/

variable {K : Type*} [CommRing K]

/-- **A realised symmetric function is invariant under renaming the alphabet.** The image of a
power sum is, coefficientwise, the indicator of the exponent vectors of the monomials `x_i^k`, and
that family is permuted by any permutation of the alphabet; the two composites are algebra
homomorphisms out of the polynomial ring `Lambda K` on the `p_k`, so agreeing on the generators is
agreeing everywhere. -/
theorem letterPerm_realisation {ι : Lambda K →ₐ[K] AlphabetSeries K} (hι : IsRealisation ι)
    (ρ : ℕ ≃ ℕ) (f : Lambda K) : letterPerm K ρ (ι f) = ι f := by
  have key : (letterPerm K ρ).comp ι = ι := by
    refine MvPolynomial.algHom_ext fun k => ?_
    have hX : (MvPolynomial.X k : Lambda K) = powerSum K (k + 1) := rfl
    rw [AlgHom.comp_apply, hX]
    refine MvPowerSeries.ext fun d => ?_
    rw [coeff_letterPerm]
    by_cases hd : ∃ j, d = Finsupp.single j (k + 1)
    · obtain ⟨j, rfl⟩ := hd
      rw [Finsupp.equivMapDomain_single, hι.coeff_pow k _, hι.coeff_pow k j]
    · have hd' : ∀ j : ℕ, d ≠ Finsupp.single j (k + 1) := fun j hj => hd ⟨j, hj⟩
      refine (hι.coeff_of_ne k _ fun j hj => ?_).trans (hι.coeff_of_ne k d hd').symm
      refine hd' (ρ j) ?_
      rw [← equivMapDomain_symm_self ρ d, hj, Finsupp.equivMapDomain_single]
  exact AlgHom.congr_fun key f

/-- **Reversal fixes a realised symmetric function.** For every realisation `ι`, every
`f : Lambda K` and every `m`, `rv_m(ι f) = tr_m(ι f)`: reversing the first `m` letters reflects the
whole alphabet and then truncates, and `ι f` is invariant under that reflection. -/
@[hjo "lem_reversal_on_symmetric"]
theorem letterReverse_realisation {ι : Lambda K →ₐ[K] AlphabetSeries K} (hι : IsRealisation ι)
    (f : Lambda K) (m : ℕ) : letterReverse K m (ι f) = letterTrunc K m (ι f) := by
  refine MvPowerSeries.ext fun d => ?_
  by_cases hd : ∀ i ∈ d.support, i < m
  · rw [coeff_letterReverse_of_support hd, coeff_letterTrunc_of_support hd]
    conv_rhs => rw [← letterPerm_realisation hι (blockRevPerm m) f]
    rw [coeff_letterPerm, blockRevPerm_symm]
  · rw [coeff_letterReverse_of_not_support hd, coeff_letterTrunc_of_not_support hd]

end HJO.Sym
