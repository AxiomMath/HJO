/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.SymbolCT
public meta import HJO.Attr

/-! # The reciprocal finite alphabet, and the separation of the top word length

This file carries out Steps 1 to 3 of the proof of `HJO.Bglx.criterionNecessary`. The
hypothesis there is that a combination of words of lengths at most `m` acts by zero; what those
three steps extract from it is a *single* family of identities at the top length `m`, one for each
`l ≥ 1`:

`⟨z₁^{-l} z₂^{-l} ⋯ z_m^{-l}⟩_m = 0`.

The device is BGLX's **reciprocal finite alphabet** `ζ_k`, the `𝕜`-algebra homomorphism `Λ → Λ[z^±]`
sending `p_j` to `z_1^{-j} + ⋯ + z_k^{-j}`. It is an alphabet of `k` letters, so it kills `e_n` for
every `n > k` and sends `e_k` to `z_1^{-1}⋯z_k^{-1}`; taking `F = e_m^{\,l}` therefore silences
every length `k < m` at once and leaves the monomial above at length `m`.

What makes `ζ_k` usable against a hypothesis stated at the *displacement* `δ^{(k)}` is the single
identity

`κ(p_j) · ζ_k(p_j) = δ^{(k)}(p_j) - p_j`,

which holds for every `j ≥ 1` because the displacement is `p_j ↦ p_j + κ(p_j)(z_1^{-j}+⋯+z_k^{-j})`
by definition. The right-hand side has `Λ`-coefficients not depending on `k`, which is the whole
point, and `κ(p_j) = (1-q^j)(1-u^j)` must be inverted — the one place a hypothesis on the parameters
enters the necessity half.

## Main definitions

* `HJO.Bglx.recipVar`: the Laurent monomial `z_i^{-1}`.
* `HJO.Bglx.alphOf`: the alphabet `∑_{i ∈ s} z_i^{-1}` for a finite set `s` of variables.
* `HJO.Bglx.finiteAlphabet`: `ζ_k`, the case `s = univ`.

## Main statements

* `HJO.Bglx.alphOf_elemSymm`: an alphabet of `#s` letters kills `e_n` for `n > #s` and sends
  `e_{#s}` to the product of its letters, the vanishing and the top value at once.
* `HJO.Bglx.smul_finiteAlphabet_powerSum`: the transport identity, which replaces the expansion of
  `ζ_k(p_λ)` over subsets of the letters.
* `HJO.Bglx.sum_symbolCT_finiteAlphabet_eq_zero`: Step 2 — the hypothesis read at the finite
  alphabet.
* `HJO.Bglx.symbolCT_monomial_eq_zero`: Step 3 — the identities at the top length.

## Implementation notes

**The induction is over the set of letters, not over the number of variables.** The target ring
`Λ[z_1^±,…,z_k^±]` depends on `k`, so an induction on `k` would change the ring at every step and
`HJO.Bglx.map_elemSymm_add` could not be applied. Working with `HJO.Bglx.alphOf s` for
`s : Finset (Fin k)` inside a *fixed* ring removes that obstruction, and `ζ_k` is the case
`s = univ`. The two conclusions of `alphOf_elemSymm` are proved by one induction because each step
uses both.

**The expansion of `ζ_k(p_λ)` over subsets of the letters is not needed.** That expansion
exists to write `ζ_k(p_λ)` as a combination of the `δ^{(k)}(p_μ)` with
`k`-independent coefficients, so that the hypothesis may be applied term by term. The same effect is
got by carrying the multipliers through an induction on `F` — the statement proved is
`∀ a G, ∑_k ⟨a · δ^{(k)}(G) · ζ_k(F)⟩_k = 0`, and the inductive step
`F ↦ F p_j` moves `p_j` either into `G` or into `a`, which is exactly the two-term split the
transport identity offers. `MvPolynomial.induction_on` then needs no subsets, no multisets and no
partitions, and this is shorter than the route through the expansion.

**The hypothesis on the parameters is exactly `κ(p_j) ≠ 0` for every `j ≥ 1`**, i.e.
`q^j ≠ 1` and `u^j ≠ 1`; nothing stronger is used anywhere below, and nothing weaker will do, the
identity being divided by that scalar. The criterion as usually stated omits it, which is
the defect recorded in the module docstring of `HJO/Collinear/SymbolSym.lean`.

## References

The reference is F. Bergeron, A. M. Garsia, E. Leven and G. Xin, *Some
remarkable new plethystic operators in the theory of Macdonald polynomials*, arXiv:1405.0316v1,
J. Comb. **7** (2016) 671--714, whose equation (2.13) is the identity Step 2 produces.
-/

@[expose] public section

namespace HJO.Bglx

open HJO.Sym

variable {K : Type*} [CommRing K] [Algebra ℚ K] {k : ℕ}

/-! ### The letters of the finite alphabet -/

/-- The Laurent monomial `z_i^{-1}`, one letter of BGLX's alphabet `Z^{(-1)}_k`. -/
noncomputable def recipVar (K : Type*) [CommRing K] {k : ℕ} (i : Fin k) : LaurentLambda K k :=
  AddMonoidAlgebra.single (Finsupp.single i (-1 : ℤ)) 1

omit [Algebra ℚ K] in
/-- The powers of a letter are the negative powers of the variable. -/
lemma recipVar_pow (i : Fin k) (j : ℕ) :
    recipVar K i ^ j = AddMonoidAlgebra.single (Finsupp.single i (-(j : ℤ))) 1 := by
  rw [recipVar, AddMonoidAlgebra.single_pow, one_pow]
  congr 1
  simp

omit [Algebra ℚ K] in
/-- A finite product of Laurent monomials with unit coefficient is the monomial at the sum of the
exponents. -/
lemma prod_single_one {ι : Type*} (s : Finset ι) (b : ι → Fin k →₀ ℤ) :
    ∏ i ∈ s, (AddMonoidAlgebra.single (b i) (1 : Lambda K))
      = AddMonoidAlgebra.single (∑ i ∈ s, b i) 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp [AddMonoidAlgebra.one_def]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ih, AddMonoidAlgebra.single_mul_single, Finset.sum_insert ha,
      one_mul]

/-! ### The alphabet of a finite set of variables -/

/-- The alphabet `∑_{i ∈ s} z_i^{-1}`: the `𝕜`-algebra homomorphism `Λ → Λ[z^±]` sending `p_j` to
`∑_{i ∈ s} z_i^{-j}`. `HJO.Bglx.finiteAlphabet` is the case `s = univ`; the general case exists so
that the values on the elementary symmetric functions can be proved by induction on `s` inside a
fixed target ring. -/
noncomputable def alphOf (K : Type*) [CommRing K] {k : ℕ} (s : Finset (Fin k)) :
    Lambda K →ₐ[K] LaurentLambda K k :=
  MvPolynomial.aeval fun n => ∑ i ∈ s, recipVar K i ^ (n + 1)

omit [Algebra ℚ K] in
/-- The value of the alphabet on a power sum. -/
theorem alphOf_powerSum (s : Finset (Fin k)) {j : ℕ} (hj : 1 ≤ j) :
    alphOf K s (powerSum K j) = ∑ i ∈ s, recipVar K i ^ j := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  rw [powerSum, Nat.add_sub_cancel, alphOf, MvPolynomial.aeval_X]

omit [Algebra ℚ K] in
/-- The alphabet of a single letter. -/
theorem alphOf_singleton_powerSum (a : Fin k) {j : ℕ} (hj : 1 ≤ j) :
    alphOf K {a} (powerSum K j) = recipVar K a ^ j := by
  rw [alphOf_powerSum {a} hj, Finset.sum_singleton]

/-- **The values of a finite alphabet on the elementary symmetric functions.** An alphabet of `#s`
letters kills `e_n` for every `n > #s`, and sends `e_{#s}` to the product of its letters. The two
statements are proved together because each step of the induction on `s` uses both. -/
@[hjo "lem_bglx_finite_alphabet_esymm_vanish", hjo "lem_bglx_finite_alphabet_esymm_top"]
theorem alphOf_elemSymm (K : Type*) [CommRing K] [Algebra ℚ K] {k : ℕ} (s : Finset (Fin k)) :
    (∀ n : ℕ, s.card < n → alphOf K s (elemSymm K n) = 0)
      ∧ alphOf K s (elemSymm K s.card) = ∏ i ∈ s, recipVar K i := by
  classical
  induction s using Finset.induction with
  | empty =>
    have hp : ∀ j : ℕ, 1 ≤ j →
        alphOf K (∅ : Finset (Fin k)) (powerSum K j) = (0 : LaurentLambda K k) ^ j := by
      intro j hj
      rw [alphOf_powerSum ∅ hj, Finset.sum_empty, zero_pow (by omega)]
    have hval := map_elemSymm_geom (0 : LaurentLambda K k) (alphOf K (∅ : Finset (Fin k))) hp
    refine ⟨fun n hn => ?_, ?_⟩
    · rw [hval n, ite_eq_right (by rw [Finset.card_empty] at hn; omega)]
      split_ifs <;> rfl
    · rw [Finset.card_empty, hval 0, ite_eq_left rfl, Finset.prod_empty]
  | insert a s ha ih =>
    have hp : ∀ j : ℕ, 1 ≤ j → alphOf K (insert a s) (powerSum K j)
        = alphOf K s (powerSum K j) + alphOf K {a} (powerSum K j) := by
      intro j hj
      rw [alphOf_powerSum _ hj, alphOf_powerSum _ hj, alphOf_powerSum _ hj,
        Finset.sum_insert ha, Finset.sum_singleton, add_comm]
    have hgeom : ∀ t : ℕ, alphOf K {a} (elemSymm K t)
        = if t = 0 then 1 else if t = 1 then recipVar K a else 0 :=
      map_elemSymm_geom (recipVar K a) (alphOf K {a})
        fun j hj => alphOf_singleton_powerSum a hj
    have hstep : ∀ n : ℕ, alphOf K (insert a s) (elemSymm K (n + 1))
        = alphOf K s (elemSymm K (n + 1)) + alphOf K s (elemSymm K n) * recipVar K a := by
      intro n
      have hhigh : ∀ t ∈ Finset.range (n + 1 + 1), t ∉ Finset.range 2 →
          alphOf K s (elemSymm K (n + 1 - t)) * alphOf K {a} (elemSymm K t) = 0 := by
        intro t _ ht
        rw [Finset.mem_range] at ht
        rw [hgeom t, ite_eq_right (by omega), ite_eq_right (by omega), mul_zero]
      rw [map_elemSymm_add (alphOf K s) (alphOf K {a}) (alphOf K (insert a s)) hp (n + 1),
        ← Finset.sum_subset (show Finset.range 2 ⊆ Finset.range (n + 1 + 1) from fun t ht => by
          rw [Finset.mem_range] at ht ⊢; omega) hhigh,
        Finset.sum_range_succ, Finset.sum_range_one, hgeom 0, hgeom 1]
      simp
    have hcard : (insert a s).card = s.card + 1 := Finset.card_insert_of_notMem ha
    refine ⟨fun n hn => ?_, ?_⟩
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by rw [hcard] at hn; omega⟩
      rw [hstep n', ih.1 (n' + 1) (by rw [hcard] at hn; omega),
        ih.1 n' (by rw [hcard] at hn; omega), zero_mul, add_zero]
    · rw [hcard, hstep s.card, ih.1 (s.card + 1) (by omega), ih.2, zero_add,
        Finset.prod_insert ha, mul_comm]

/-! ### The reciprocal finite alphabet -/

/-- **BGLX's reciprocal finite alphabet** `ζ_k`: the `𝕜`-algebra homomorphism `Λ → Λ[z^±]` sending
`p_j` to `z_1^{-j} + ⋯ + z_k^{-j}`. It is *not* the displacement of
`HJO.Sym.plethShiftMulti`, which adds an alphabet to `X` where this one replaces `X` altogether. -/
@[hjo "def_bglx_finite_alphabet"]
noncomputable def finiteAlphabet (K : Type*) [CommRing K] (k : ℕ) :
    Lambda K →ₐ[K] LaurentLambda K k :=
  alphOf K Finset.univ

omit [Algebra ℚ K] in
/-- The value of `ζ_k` on a power sum, which is the definition of it. -/
@[hjo "def_bglx_finite_alphabet"]
theorem finiteAlphabet_powerSum {j : ℕ} (hj : 1 ≤ j) :
    finiteAlphabet K k (powerSum K j) = ∑ i : Fin k, recipVar K i ^ j :=
  alphOf_powerSum Finset.univ hj

/-- **`ζ_k` kills the elementary symmetric functions above degree `k`**: an alphabet of `k` letters
has no `e_n` for `n > k`. -/
@[hjo "lem_bglx_finite_alphabet_esymm_vanish"]
theorem finiteAlphabet_elemSymm_eq_zero {n : ℕ} (hn : k < n) :
    finiteAlphabet K k (elemSymm K n) = 0 :=
  (alphOf_elemSymm K Finset.univ).1 n (by rwa [Finset.card_univ, Fintype.card_fin])

/-- **`ζ_k` sends `e_k` to `z_1^{-1} z_2^{-1} ⋯ z_k^{-1}`**, the only `k`-element subset of a
`k`-letter alphabet being the whole of it. -/
@[hjo "lem_bglx_finite_alphabet_esymm_top"]
theorem finiteAlphabet_elemSymm_self (K : Type*) [CommRing K] [Algebra ℚ K] (k : ℕ) :
    finiteAlphabet K k (elemSymm K k) = AddMonoidAlgebra.single (-allOnes k) 1 := by
  have h := (alphOf_elemSymm K (Finset.univ : Finset (Fin k))).2
  rw [Finset.card_univ, Fintype.card_fin] at h
  have hprod : (∏ i : Fin k, recipVar K i)
      = AddMonoidAlgebra.single (∑ i : Fin k, Finsupp.single i (-1 : ℤ)) (1 : Lambda K) :=
    prod_single_one Finset.univ fun i : Fin k => Finsupp.single i (-1 : ℤ)
  rw [finiteAlphabet, h, hprod]
  congr 1
  rw [allOnes_eq_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [← Finsupp.single_neg]

/-! ### The transport identity -/

omit [Algebra ℚ K] in
/-- **The transport identity**: for every `j ≥ 1`,
`κ(p_j) ζ_k(p_j) = δ^{(k)}(p_j) - p_j`. This is the displacement's own definition read backwards,
and it is what lets a hypothesis stated at `δ^{(k)}` be read at `ζ_k`: the right-hand side has
`Λ`-coefficients that do not depend on `k`. It replaces the expansion of `ζ_k(p_λ)` over subsets
of the letters. -/
@[hjo "lem_bglx_finite_alphabet_expand"]
theorem smul_finiteAlphabet_powerSum (q u : K) (k : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    paramPleth q u (powerSum K j) • finiteAlphabet K k (powerSum K j)
      = plethShiftMulti q u k (powerSum K j) - laurentLambdaC K k (powerSum K j) := by
  rw [plethShiftMulti_powerSum q u k hj, laurentLambdaC_apply, add_sub_cancel_left,
    finiteAlphabet_powerSum hj, Finset.smul_sum, paramPleth_powerSum q u hj]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [recipVar_pow]
  exact (AddMonoidAlgebra.smul_single _ _ _).trans
    (by rw [Algebra.smul_def, mul_one, MvPolynomial.algebraMap_eq])

end HJO.Bglx
