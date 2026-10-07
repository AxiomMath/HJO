/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CharSeries
public import HJO.CarlssonMellit.TwoLetterChar
public meta import HJO.Attr

/-! # The characteristic series is symmetric in two neighbouring letters

Carlsson--Mellit's Proposition 3.2: for a transitive attack set `R` on `{1, …, n}` the series
`χ(R, n)` is invariant under the automorphism of `𝒫` interchanging `x_i` and `x_{i+1}` and fixing
every other letter.

The proof groups the labellings `w` by the *block* data `(S, f)`, where `S = {l : w_l ∈ {i, i+1}}`
and `f` is the restriction of `w` off `S`. On one block the inversions split: those internal to `S`
are the inversions of the restricted attack set `R_S` read on the two-letter word recording which of
`i`, `i+1` stands at each position of `S`, and those not internal to `S` are the same number for
every labelling of the block, because `i ⋖ i + 1`. So the block sums to
`q^c ⬝ (∏_{l ∉ S} x_{f l}) ⬝ χ₂(R_S, #S)` with `ξ₁ ↦ x_i`, `ξ₂ ↦ x_{i+1}`, and the symmetry of the
two-letter polynomial finishes it.

## Main definitions

* `HJO.Dyck.twoLetterSubst`: the `K`-algebra map `MvPolynomial (Fin 2) K → 𝒫` substituting `x_i` for
  `ξ₁` and `x_{i+1}` for `ξ₂`.
* `HJO.Dyck.blockWord`: the `v(w)`, the two-letter word a block labelling induces.
* `HJO.Dyck.blockLabelling`: the labelling a two-letter word induces, inverse to the above.

## Main results

* `HJO.Dyck.letterPerm_swap_charSeries`.
* `HJO.Dyck.sum_block_eq`: the block sum in closed form.
* `HJO.Dyck.letterPerm_swap_sum_block`: one block is invariant.

## Implementation notes

*Letters are indexed from `0`*, as everywhere in this library, so the `i ≥ 1` is an unconstrained
`i : ℕ` here: the statement as usually given numbers the letters from `1` and asks for a pair
`x_i, x_{i+1}` of *existing* letters, which on a `0`-based alphabet is every `i : ℕ`. No hypothesis
is dropped.

*The automorphism is* `HJO.Sym.letterPerm K (Equiv.swap i (i + 1))`, the renaming of the whole
alphabet along the transposition of `i` and `i + 1`; it fixes every other letter, so it is the
automorphism `ς` of the statement. Being a renaming along a permutation of `ℕ` it is an algebra
*automorphism*, which is what the word "automorphism" asks for.

*The reduction to a finite sum.* The defining sum of `χ(R, n)` has infinitely many terms, so the
whole argument runs on the honest finite sum of
`HJO.Dyck.coeff_charSeries_eq_coeff_sum_wordMonomial` over the labellings with letters in a finite
set `s`. Only `i ∈ s` and `i + 1 ∈ s` are needed: they already make `s` invariant under the
transposition, since it fixes everything else. At a given monomial `d` the set
`s = {i, i + 1} ∪ supp d` serves both `d` and its image under the transposition, which is what lets
a single finite identity decide the coefficient.

*The block data is recorded by one function* `l ↦ if w l ∈ {i, i+1} then none else some (w l)`,
whose fibres are exactly the `W_{S,f}`; `Finset.sum_fiberwise_of_maps_to` then splits
the finite sum. The `S = {s_1 < ⋯ < s_m}` is `S.orderEmbOfFin rfl`, and
`HJO.Dyck.getD_sort_image_val` identifies it with the `Finset.sort`-based enumeration that
`HJO.Dyck.attackRestrict` renumbers along, the two differing only by the coercion `Fin n → ℕ`.

*The substitution `ξ₁ ↦ x_i`, `ξ₂ ↦ x_{i+1}` is an algebra map out of a polynomial ring*, so the
one thing needed of it — that it intertwines `ξ₁ ↔ ξ₂` with `x_i ↔ x_{i+1}` — is an equality of
algebra homomorphisms, proved on the two generators by `MvPolynomial.algHom_ext`. That is
`HJO.Dyck.letterPerm_comp_twoLetterSubst`, and it is why no coefficient computation is needed to
transport `HJO.Dyck.rename_swap_twoLetterChar` into `𝒫`.

## References

This file proves `HJO.Dyck.letterPerm_swap_charSeries`, using `HJO.Sym.AlphabetSeries`,
`HJO.Dyck.attackRestrict`, `HJO.Dyck.invSet`, `HJO.Dyck.invNumber`, `HJO.Sym.wordMonomial`,
`HJO.Dyck.charSeries`, `HJO.Dyck.twoLetterChar`, `HJO.Dyck.isTransitiveAttackSet_attackRestrict`,
`HJO.Dyck.rename_swap_twoLetterChar` and `HJO.Dyck.card_filter_invSet_congr_of_covBy`. E. Carlsson
and A. Mellit, *A proof of the shuffle conjecture*, Proposition 3.2.
-/

@[expose] public section

open Finset HJO.Sym

namespace HJO.Dyck

variable {K : Type*} [CommRing K]

/-! ### Renaming the alphabet on a letter -/

/-- Renaming the alphabet along a permutation sends the letter `x_j` to `x_{ρ j}`. -/
theorem letterPerm_X (ρ : ℕ ≃ ℕ) (j : ℕ) :
    letterPerm K ρ (MvPowerSeries.X j) = (MvPowerSeries.X (ρ j) : AlphabetSeries K) := by
  change MvPowerSeries.rename (ρ.toEmbedding : ℕ → ℕ) (MvPowerSeries.X j) = _
  rw [MvPowerSeries.rename_X]
  rfl

/-! ### Substituting two neighbouring letters for the two indeterminates -/

/-- The `K`-algebra map `MvPolynomial (Fin 2) K → 𝒫` substituting the letter `x_i` for `ξ₁ = X 0`
and the letter `x_{i+1}` for `ξ₂ = X 1`: the `|_{ξ₁ = x_i, ξ₂ = x_{i+1}}`. The two
indeterminates being `Fin 2` and the two letters consecutive, it is `X t ↦ x_{i + t}`. -/
noncomputable def twoLetterSubst (K : Type*) [CommRing K] (i : ℕ) :
    MvPolynomial (Fin 2) K →ₐ[K] AlphabetSeries K :=
  MvPolynomial.aeval fun t : Fin 2 => MvPowerSeries.X (i + (t : ℕ))

@[simp]
theorem twoLetterSubst_X (i : ℕ) (t : Fin 2) :
    twoLetterSubst K i (MvPolynomial.X t) = (MvPowerSeries.X (i + (t : ℕ)) : AlphabetSeries K) :=
  MvPolynomial.aeval_X _ t

/-- **The substitution intertwines the two swaps**: interchanging the two indeterminates and then
substituting is substituting and then interchanging the two letters `x_i` and `x_{i+1}`. Both sides
are algebra maps out of a polynomial ring, so this is checked on the two generators. -/
theorem letterPerm_comp_twoLetterSubst (i : ℕ) :
    (letterPerm K (Equiv.swap i (i + 1))).comp (twoLetterSubst K i)
      = (twoLetterSubst K i).comp (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)) := by
  refine MvPolynomial.algHom_ext fun t => ?_
  fin_cases t <;>
    simp [letterPerm_X, Equiv.swap_apply_left, Equiv.swap_apply_right]

/-- The image of the two-letter polynomial under the substitution, written out: the sum over the
two-letter words `v` of `q ^ inv(R, v)` times the monomial `x_i^{#v⁻¹(0)} x_{i+1}^{#v⁻¹(1)}`. -/
theorem twoLetterSubst_twoLetterChar (q : K) (m : ℕ) (R : Finset (ℕ × ℕ)) (i : ℕ) :
    twoLetterSubst K i (twoLetterChar q m R)
      = ∑ v : Fin m → Fin 2, q ^ #(invSet (finPairs m R) v) •
          ∏ j, (MvPowerSeries.X (i + (v j : ℕ)) : AlphabetSeries K) := by
  rw [twoLetterChar, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_mul, map_prod]
  simp only [twoLetterSubst, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  rw [← Algebra.smul_def]

/-! ### The increasing enumeration of a set of positions -/

/-- Every position of `S` is reached by the increasing enumeration of `S`. -/
theorem exists_orderEmbOfFin_eq {n : ℕ} {S : Finset (Fin n)} {l : Fin n} (hl : l ∈ S) :
    ∃ j : Fin #S, S.orderEmbOfFin rfl j = l := by
  have h : l ∈ Set.range (S.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact hl
  exact h

/-- **The two enumerations of a set of positions agree.** `HJO.Dyck.attackRestrict` renumbers along
the `Finset.sort` enumeration of a set of *natural numbers*, while a set `S` of positions of
`Fin n` is enumerated by `S.orderEmbOfFin`; passing to the image of `S` in `ℕ` these are the same
map, up to the coercion `Fin n → ℕ`. Both are strictly monotone enumerations of the image, so
`Finset.orderEmbOfFin_unique` identifies them. -/
theorem getD_sort_image_val {n : ℕ} (S : Finset (Fin n)) (j : Fin #S) :
    (S.image Fin.val).sort.getD (j : ℕ) 0 = ((S.orderEmbOfFin rfl j : Fin n) : ℕ) := by
  have hcard : #(S.image Fin.val) = #S := Finset.card_image_of_injective _ Fin.val_injective
  have hlt : ∀ x : Fin #S, (x : ℕ) < #(S.image Fin.val) := fun x => by rw [hcard]; exact x.2
  have h1 : (fun j : Fin #S => (S.image Fin.val).sort.getD (j : ℕ) 0)
      = (S.image Fin.val).orderEmbOfFin hcard :=
    Finset.orderEmbOfFin_unique hcard (fun x => Finset.getD_sort_mem _ _ (hlt x))
      fun a b hab => (Finset.getD_sort_lt_getD_sort_iff _ 0 (hlt a) (hlt b)).2 hab
  have h2 : (fun j : Fin #S => ((S.orderEmbOfFin rfl j : Fin n) : ℕ))
      = (S.image Fin.val).orderEmbOfFin hcard :=
    Finset.orderEmbOfFin_unique hcard
      (fun x => Finset.mem_image_of_mem _ (S.orderEmbOfFin_mem rfl x))
      fun a b hab => (S.orderEmbOfFin rfl).strictMono hab
  exact congrFun (h1.trans h2.symm) j

/-! ### One block of labellings -/

variable {n : ℕ} {R : Finset (ℕ × ℕ)} {i : ℕ} {S : Finset (Fin n)} {f w : Fin n → ℕ}
  {W : Finset (Fin n → ℕ)}

/-- The `v(w)`: the two-letter word recording, at the `j`-th position of `S`, which of
the two letters `i`, `i + 1` the labelling `w` puts there. -/
def blockWord (i : ℕ) (S : Finset (Fin n)) (w : Fin n → ℕ) (j : Fin #S) : Fin 2 :=
  if w (S.orderEmbOfFin rfl j) = i then 0 else 1

/-- The labelling of a block determined by a two-letter word: `i` or `i + 1` at the `j`-th position
of `S` according to `v j`, and `f` off `S`. On a block this inverts `HJO.Dyck.blockWord`. -/
noncomputable def blockLabelling (i : ℕ) (S : Finset (Fin n)) (f : Fin n → ℕ) (v : Fin #S → Fin 2)
    (l : Fin n) : ℕ :=
  if h : ∃ j : Fin #S, S.orderEmbOfFin rfl j = l then i + (v h.choose : ℕ) else f l

/-- On a block, the letter at the `j`-th position of `S` is read off the two-letter word. -/
theorem add_blockWord (hS : ∀ l, (w l = i ∨ w l = i + 1) ↔ l ∈ S) (j : Fin #S) :
    i + (blockWord i S w j : ℕ) = w (S.orderEmbOfFin rfl j) := by
  rw [blockWord]
  rcases (hS _).2 (S.orderEmbOfFin_mem rfl j) with h | h
  · rw [ite_eq_left h, h]; simp
  · rw [ite_eq_right (by omega : ¬ (w (S.orderEmbOfFin rfl j) = i)), h]; simp

/-- On a block, an internal pair is inverted by the labelling exactly when the two-letter word
inverts it. -/
theorem blockWord_lt_blockWord (hS : ∀ l, (w l = i ∨ w l = i + 1) ↔ l ∈ S) (j j' : Fin #S) :
    blockWord i S w j' < blockWord i S w j
      ↔ w (S.orderEmbOfFin rfl j') < w (S.orderEmbOfFin rfl j) := by
  rw [← add_blockWord hS j, ← add_blockWord hS j', add_lt_add_iff_left, Fin.lt_def]

/-- The labelling built from a two-letter word carries that word's letters on the block. -/
theorem blockLabelling_orderEmbOfFin (f : Fin n → ℕ) (v : Fin #S → Fin 2) (j : Fin #S) :
    blockLabelling i S f v (S.orderEmbOfFin rfl j) = i + (v j : ℕ) := by
  have h : ∃ j' : Fin #S, S.orderEmbOfFin rfl j' = S.orderEmbOfFin rfl j := ⟨j, rfl⟩
  have hj : h.choose = j := (S.orderEmbOfFin rfl).injective h.choose_spec
  rw [blockLabelling, dite_eq_left h, hj]

/-- The labelling built from a two-letter word agrees with `f` off the block. -/
theorem blockLabelling_of_not_mem (f : Fin n → ℕ) (v : Fin #S → Fin 2) {l : Fin n} (hl : l ∉ S) :
    blockLabelling i S f v l = f l :=
  dite_eq_right fun ⟨j, hj⟩ => hl (hj ▸ S.orderEmbOfFin_mem rfl j)

/-- **The inversions internal to a block are the inversions of the restricted attack set.** Under
the bijection `w ↦ v(w)` the pairs of `R` internal to `S` that `w` inverts correspond
to the pairs of `R_S` that `v(w)` inverts, the enumeration of `S` being order-reflecting. -/
theorem card_filter_invSet_eq (hR : ∀ p ∈ R, p.1 < p.2)
    (hS : ∀ l, (w l = i ∨ w l = i + 1) ↔ l ∈ S) :
    #{p ∈ invSet (finPairs n R) w | p.1 ∈ S ∧ p.2 ∈ S}
      = #(invSet (finPairs #S (attackRestrict R (S.image Fin.val))) (blockWord i S w)) := by
  classical
  have hcard : #(S.image Fin.val) = #S := Finset.card_image_of_injective _ Fin.val_injective
  have hmem : ∀ p : Fin #S × Fin #S,
      (p ∈ invSet (finPairs #S (attackRestrict R (S.image Fin.val))) (blockWord i S w)
        ↔ (S.orderEmbOfFin rfl p.1, S.orderEmbOfFin rfl p.2)
            ∈ {p ∈ invSet (finPairs n R) w | p.1 ∈ S ∧ p.2 ∈ S}) := fun p => by
    simp only [mem_invSet, mem_finPairs, mem_filter,
      mem_attackRestrict_iff_of_forall_lt hR, getD_sort_image_val, hcard,
      blockWord_lt_blockWord hS, Finset.orderEmbOfFin_mem, and_true, Fin.is_lt, true_and]
  refine (Finset.card_nbij (fun p => (S.orderEmbOfFin rfl p.1, S.orderEmbOfFin rfl p.2))
    (fun p hp => (hmem p).1 hp) (fun p _ p' _ h => ?_) fun p hp => ?_).symm
  · exact Prod.ext ((S.orderEmbOfFin rfl).injective (congrArg Prod.fst h))
      ((S.orderEmbOfFin rfl).injective (congrArg Prod.snd h))
  · obtain ⟨hp1, hp2, hp3⟩ := mem_filter.1 (Finset.mem_coe.1 hp)
    obtain ⟨j, hj⟩ := exists_orderEmbOfFin_eq hp2
    obtain ⟨j', hj'⟩ := exists_orderEmbOfFin_eq hp3
    refine ⟨(j, j'), (hmem (j, j')).2 ?_, Prod.ext hj hj'⟩
    rw [show (S.orderEmbOfFin rfl j, S.orderEmbOfFin rfl j') = p from Prod.ext hj hj']
    exact Finset.mem_coe.1 hp

/-- **The block sum in closed form**:
`χ_{S,f} = q^c (∏_{l ∉ S} x_{f l}) χ₂(R_S, #S)|_{ξ₁ = x_i, ξ₂ = x_{i+1}}`. -/
theorem sum_block_eq (q : K) (hR : IsTransitiveAttackSet n R)
    (hW : ∀ w, w ∈ W ↔ ((∀ l, (w l = i ∨ w l = i + 1) ↔ l ∈ S) ∧ ∀ l ∉ S, w l = f l))
    {w₀ : Fin n → ℕ} (hw₀ : w₀ ∈ W) :
    ∑ w ∈ W, q ^ #(invSet (finPairs n R) w) • wordMonomial K w
      = q ^ #{p ∈ invSet (finPairs n R) w₀ | ¬(p.1 ∈ S ∧ p.2 ∈ S)} •
          ((∏ l ∈ Sᶜ, (MvPowerSeries.X (f l) : AlphabetSeries K)) *
            twoLetterSubst K i (twoLetterChar q #S (attackRestrict R (S.image Fin.val)))) := by
  classical
  have hcov : i ⋖ i + 1 := ⟨Nat.lt_succ_self i, fun c h1 h2 => by omega⟩
  obtain ⟨hw₀S, hw₀f⟩ := (hW w₀).1 hw₀
  have hfne : ∀ l ∉ S, ¬(f l = i ∨ f l = i + 1) := fun l hl hc =>
    hl ((hw₀S l).1 (by rwa [hw₀f l hl]))
  set c := #{p ∈ invSet (finPairs n R) w₀ | ¬(p.1 ∈ S ∧ p.2 ∈ S)} with hc
  -- the exponent of `q` on the block
  have hexp : ∀ w ∈ W, #(invSet (finPairs n R) w)
      = c + #(invSet (finPairs #S (attackRestrict R (S.image Fin.val))) (blockWord i S w)) := by
    intro w hw
    have hcw : #{p ∈ invSet (finPairs n R) w | ¬(p.1 ∈ S ∧ p.2 ∈ S)} = c :=
      card_filter_invSet_congr_of_covBy hcov _ S ((hW w).1 hw).1 hw₀S
        fun l hl => (hw₀f l hl).trans (((hW w).1 hw).2 l hl).symm
    rw [← card_filter_invSet_eq hR.fst_lt_snd ((hW w).1 hw).1, ← hcw, add_comm,
      Finset.card_filter_add_card_filter_not]
  -- the monomial on the block
  have hmon : ∀ w ∈ W, wordMonomial K w
      = (∏ l ∈ Sᶜ, (MvPowerSeries.X (f l) : AlphabetSeries K)) *
          ∏ j, (MvPowerSeries.X (i + (blockWord i S w j : ℕ)) : AlphabetSeries K) := by
    intro w hw
    rw [wordMonomial_eq_prod_mul_prod_compl w S, mul_comm]
    congr 1
    · exact Finset.prod_congr rfl fun l hl =>
        congrArg MvPowerSeries.X (((hW w).1 hw).2 l (Finset.mem_compl.1 hl))
    · refine (Finset.prod_nbij (fun j => S.orderEmbOfFin rfl j)
        (fun j _ => S.orderEmbOfFin_mem rfl j)
        (fun a _ b _ h => (S.orderEmbOfFin rfl).injective h) (fun l hl => ?_) fun j _ => ?_).symm
      · obtain ⟨j, hj⟩ := exists_orderEmbOfFin_eq (Finset.mem_coe.1 hl)
        exact ⟨j, Finset.mem_coe.2 (Finset.mem_univ j), hj⟩
      · exact congrArg MvPowerSeries.X (add_blockWord ((hW w).1 hw).1 j)
  rw [twoLetterSubst_twoLetterChar, Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_nbij (blockWord i S) (fun w _ => Finset.mem_univ _)
    (fun w hw w' hw' h => ?_) (fun v _ => ?_) fun w hw => ?_
  -- the two-letter word determines the labelling of the block
  · rw [Finset.mem_coe, hW] at hw hw'
    refine funext fun l => ?_
    by_cases hl : l ∈ S
    · obtain ⟨j, hj⟩ := exists_orderEmbOfFin_eq hl
      rw [← hj, ← add_blockWord hw.1 j, ← add_blockWord hw'.1 j, h]
    · rw [hw.2 l hl, hw'.2 l hl]
  -- every two-letter word comes from a labelling of the block
  · refine ⟨blockLabelling i S f v, Finset.mem_coe.2 ((hW _).2 ⟨fun l => ?_, fun l hl =>
      blockLabelling_of_not_mem f v hl⟩), funext fun j => ?_⟩
    · constructor
      · intro hmem
        by_contra hl
        rw [blockLabelling_of_not_mem f v hl] at hmem
        exact hfne l hl hmem
      · intro hl
        obtain ⟨j, hj⟩ := exists_orderEmbOfFin_eq hl
        rw [← hj, blockLabelling_orderEmbOfFin]
        have : (v j : ℕ) = 0 ∨ (v j : ℕ) = 1 := by omega
        rcases this with h | h <;> rw [h] <;> omega
    · rw [blockWord, blockLabelling_orderEmbOfFin]
      have : (v j : ℕ) = 0 ∨ (v j : ℕ) = 1 := by omega
      rcases this with h | h
      · rw [ite_eq_left (by omega), ← Fin.val_eq_val, h]; rfl
      · rw [ite_eq_right (by omega), ← Fin.val_eq_val, h]; rfl
  -- the terms match
  · rw [hexp w hw, hmon w hw, pow_add, mul_smul, mul_smul_comm]

/-- **One block is invariant.** The last step: the substituted two-letter polynomial is
invariant by `HJO.Dyck.rename_swap_twoLetterChar`, and the letters off the block are fixed because
they are neither `i` nor `i + 1`. -/
theorem letterPerm_swap_sum_block (q : K) (hR : IsTransitiveAttackSet n R)
    (hW : ∀ w, w ∈ W ↔ ((∀ l, (w l = i ∨ w l = i + 1) ↔ l ∈ S) ∧ ∀ l ∉ S, w l = f l))
    {w₀ : Fin n → ℕ} (hw₀ : w₀ ∈ W) :
    letterPerm K (Equiv.swap i (i + 1))
        (∑ w ∈ W, q ^ #(invSet (finPairs n R) w) • wordMonomial K w)
      = ∑ w ∈ W, q ^ #(invSet (finPairs n R) w) • wordMonomial K w := by
  classical
  obtain ⟨hw₀S, hw₀f⟩ := (hW w₀).1 hw₀
  have hfne : ∀ l ∉ S, ¬(f l = i ∨ f l = i + 1) := fun l hl hc =>
    hl ((hw₀S l).1 (by rwa [hw₀f l hl]))
  have hcard : #(S.image Fin.val) = #S := Finset.card_image_of_injective _ Fin.val_injective
  have hR₂ : IsTransitiveAttackSet #S (attackRestrict R (S.image Fin.val)) := by
    rw [← hcard]; exact isTransitiveAttackSet_attackRestrict (S.image Fin.val) hR
  have hfix : ∀ l ∈ Sᶜ, letterPerm K (Equiv.swap i (i + 1)) (MvPowerSeries.X (f l))
      = (MvPowerSeries.X (f l) : AlphabetSeries K) := by
    intro l hl
    have h := hfne l (Finset.mem_compl.1 hl)
    rw [letterPerm_X, Equiv.swap_apply_of_ne_of_ne (fun hc => h (Or.inl hc))
      fun hc => h (Or.inr hc)]
  have hsubst : letterPerm K (Equiv.swap i (i + 1))
      (twoLetterSubst K i (twoLetterChar q #S (attackRestrict R (S.image Fin.val))))
      = twoLetterSubst K i (twoLetterChar q #S (attackRestrict R (S.image Fin.val))) := by
    have h := AlgHom.congr_fun (letterPerm_comp_twoLetterSubst (K := K) i)
      (twoLetterChar q #S (attackRestrict R (S.image Fin.val)))
    rw [AlgHom.comp_apply, AlgHom.comp_apply] at h
    rw [h, rename_swap_twoLetterChar q hR₂]
  rw [sum_block_eq q hR hW hw₀, map_smul, map_mul, map_prod, Finset.prod_congr rfl hfix, hsubst]

/-! ### The finite sum over a set of letters -/

/-- **The finite sum over the labellings with letters in `s` is invariant.** The labellings are
grouped by the block data — which positions carry `i` or `i + 1`, and which letters stand off those
positions — and each block is invariant by `HJO.Dyck.letterPerm_swap_sum_block`. -/
theorem letterPerm_swap_sum_wordMonomial (q : K) (hR : IsTransitiveAttackSet n R) (i : ℕ)
    {s : Finset ℕ} (hi : i ∈ s) (hi1 : i + 1 ∈ s) :
    letterPerm K (Equiv.swap i (i + 1))
        (∑ w ∈ Fintype.piFinset fun _ : Fin n => s,
          q ^ #(invSet (finPairs n R) w) • wordMonomial K w)
      = ∑ w ∈ Fintype.piFinset fun _ : Fin n => s,
          q ^ #(invSet (finPairs n R) w) • wordMonomial K w := by
  classical
  set g : (Fin n → ℕ) → Fin n → Option ℕ :=
    fun w l => if w l = i ∨ w l = i + 1 then none else some (w l) with hg
  -- two labellings have the same block data exactly when they have the same block and agree off it
  have hgiff : ∀ w w' : Fin n → ℕ, g w = g w' ↔
      ((∀ l, (w l = i ∨ w l = i + 1) ↔ (w' l = i ∨ w' l = i + 1)) ∧
        ∀ l, ¬(w' l = i ∨ w' l = i + 1) → w l = w' l) := by
    intro w w'
    rw [hg]
    simp only [funext_iff]
    constructor
    · intro h
      refine ⟨fun l => ?_, fun l hl => ?_⟩
      · have hl' := h l
        by_cases h1 : w l = i ∨ w l = i + 1
        · by_cases h2 : w' l = i ∨ w' l = i + 1
          · exact iff_of_true h1 h2
          · rw [ite_eq_left h1, ite_eq_right h2] at hl'; exact absurd hl' (by simp)
        · by_cases h2 : w' l = i ∨ w' l = i + 1
          · rw [ite_eq_right h1, ite_eq_left h2] at hl'; exact absurd hl' (by simp)
          · exact iff_of_false h1 h2
      · have hl' := h l
        rw [ite_eq_right hl] at hl'
        by_cases h1 : w l = i ∨ w l = i + 1
        · rw [ite_eq_left h1] at hl'; exact absurd hl' (by simp)
        · rw [ite_eq_right h1] at hl'; exact Option.some_injective _ hl'
    · rintro ⟨h1, h2⟩ l
      by_cases hl : w' l = i ∨ w' l = i + 1
      · rw [ite_eq_left ((h1 l).2 hl), ite_eq_left hl]
      · rw [ite_eq_right (fun hc => hl ((h1 l).1 hc)), ite_eq_right hl, h2 l hl]
  rw [← Finset.sum_fiberwise_of_maps_to
      (t := (Fintype.piFinset fun _ : Fin n => s).image g)
      (fun w hw => Finset.mem_image_of_mem g hw)
      (fun w => q ^ #(invSet (finPairs n R) w) • wordMonomial K w), map_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  obtain ⟨w₀, hw₀P, rfl⟩ := Finset.mem_image.1 hy
  have hSmem : ∀ l : Fin n,
      l ∈ ({l : Fin n | w₀ l = i ∨ w₀ l = i + 1} : Finset (Fin n)) ↔ (w₀ l = i ∨ w₀ l = i + 1) :=
    fun l => mem_filter_univ l
  have hW : ∀ w, w ∈ {w ∈ Fintype.piFinset (fun _ : Fin n => s) | g w = g w₀} ↔
      ((∀ l, (w l = i ∨ w l = i + 1) ↔ l ∈ ({l : Fin n | w₀ l = i ∨ w₀ l = i + 1} : Finset (Fin n)))
        ∧ ∀ l ∉ ({l : Fin n | w₀ l = i ∨ w₀ l = i + 1} : Finset (Fin n)), w l = w₀ l) := by
    intro w
    rw [Finset.mem_filter, hgiff]
    constructor
    · rintro ⟨-, h1, h2⟩
      exact ⟨fun l => (h1 l).trans (hSmem l).symm, fun l hl => h2 l fun hc => hl ((hSmem l).2 hc)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, fun l => (h1 l).trans (hSmem l), fun l hl => h2 l fun hc => hl ((hSmem l).1 hc)⟩
      rw [Fintype.mem_piFinset]
      intro l
      by_cases hl : l ∈ ({l : Fin n | w₀ l = i ∨ w₀ l = i + 1} : Finset (Fin n))
      · rcases (h1 l).2 hl with h | h <;> rw [h] <;> assumption
      · rw [h2 l hl]; exact Fintype.mem_piFinset.1 hw₀P l
  exact letterPerm_swap_sum_block q hR hW ((hW w₀).2 ⟨fun l => (hSmem l).symm, fun _ _ => rfl⟩)

/-! ### The characteristic series is symmetric -/

/-- **The characteristic series is symmetric.** For every transitive attack
set `R` on `{1, …, n}` and every letter `i`, the series `χ(R, n)` is invariant under the
automorphism of `𝒫` interchanging `x_i` and `x_{i+1}` and fixing every other letter.

At a monomial `d` both `d` and its image under the transposition are supported in the finite set
`{i, i + 1} ∪ supp d`, so the coefficient is decided by the finite identity
`HJO.Dyck.letterPerm_swap_sum_wordMonomial` there. -/
@[hjo "lem_cm_chi_symmetric"]
theorem letterPerm_swap_charSeries {K : Type*} [CommRing K] (q : K) {n : ℕ} {R : Finset (ℕ × ℕ)}
    (hR : IsTransitiveAttackSet n R) (i : ℕ) :
    HJO.Sym.letterPerm K (Equiv.swap i (i + 1)) (charSeries q n R) = charSeries q n R := by
  classical
  have hsymm : (Equiv.swap i (i + 1)).symm = Equiv.swap i (i + 1) := Equiv.symm_swap _ _
  refine MvPowerSeries.ext fun d => ?_
  have hi : i ∈ insert i (insert (i + 1) d.support) := Finset.mem_insert_self _ _
  have hi1 : i + 1 ∈ insert i (insert (i + 1) d.support) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hsub : ∀ j : ℕ, j ∈ d.support → j ∈ insert i (insert (i + 1) d.support) := fun j hj =>
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hj)
  have hd's : (Finsupp.equivMapDomain (Equiv.swap i (i + 1)) d).support
      ⊆ insert i (insert (i + 1) d.support) := by
    intro j hj
    rw [Finsupp.mem_support_iff, Finsupp.equivMapDomain_apply, hsymm] at hj
    by_cases h1 : j = i
    · exact h1 ▸ hi
    · by_cases h2 : j = i + 1
      · exact h2 ▸ hi1
      · exact hsub j (by
          rwa [Finsupp.mem_support_iff, ← Equiv.swap_apply_of_ne_of_ne (a := i) (b := i + 1) h1 h2])
  rw [HJO.Sym.coeff_letterPerm, hsymm, coeff_charSeries_eq_coeff_sum_wordMonomial hd's,
    coeff_charSeries_eq_coeff_sum_wordMonomial hsub, ← hsymm, ← HJO.Sym.coeff_letterPerm]
  exact congrArg (fun G => MvPowerSeries.coeff d G)
    (letterPerm_swap_sum_wordMonomial q hR i hi hi1)

end HJO.Dyck
