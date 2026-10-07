/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.CutAlphabet
public import HJO.Macdonald.MonomialBasis
public meta import HJO.Attr

/-! # Erasing a variable in a monomial symmetric polynomial

`MvPolynomial.killCompl_msymm`: `cut_n(m_μ[X_{n+1}])` is `m_μ[X_n]` when `μ_{n+1} = 0` and `0`
when `μ_{n+1} ≥ 1`.

## The two cases are one identity

Mathlib's `MvPolynomial.msymm σ R μ` is indexed by `μ : Nat.Partition d`, the *degree* `d` being
the size of the partition, and is the sum of `∏ᵢ x_{aᵢ}` over the multisets `a : Sym σ d` whose
multiset of multiplicities is `μ.parts`. The number of nonzero entries of `μ`, written as a
sequence `μ_1 ≥ μ_2 ≥ …`, is therefore `μ.parts.card`, and the index conditions read
`μ_{n+1} = 0 ↔ μ.parts.card ≤ n` and `μ_{n+1} ≥ 1 ↔ n < μ.parts.card`.

In that indexing the two cases collapse into a single unconditional identity, for an arbitrary
injection `f : σ → τ` of finite alphabets:
```
killCompl hf (msymm τ R μ) = msymm σ R μ
```
A monomial `∏ᵢ x_{aᵢ}` of `msymm τ R μ` survives `killCompl hf` exactly when every element of the
multiset `a` lies in the range of `f`, and those `a` are precisely the `Sym.map f b` for
`b : Sym σ d`, with `Nat.Partition.ofSym (Sym.map f b) = Nat.Partition.ofSym b`
(`Nat.Partition.ofSym_map_of_injective`); so the surviving sub-sum is `msymm σ R μ` term by term.
The second case is then *not a separate argument* but the observation that the target
is zero when the partition does not fit in the small alphabet: `Nat.Partition.ofSym b` has at most
`#σ` parts, so the index set of `msymm σ R μ` is empty
(`MvPolynomial.msymm_eq_zero_of_card_lt`, on `Nat.Partition.parts_card_le`).

## Generality, and the hypotheses that are dropped

The statement carries no parameters: `q` and `u` do not occur, so nothing here needs the standing
algebraic independence, and `R` is an arbitrary commutative *semiring*. As in
`HJO/Macdonald/CutAlphabet.lean` the map is `MvPolynomial.killCompl hf` for an arbitrary
injection `f : σ → τ` of finite alphabets — the map `cut_n` is the case `σ = Fin n`,
`τ = Fin (n + 1)`, `f = Fin.castSucc` — so a hypothesis `n ≥ 1` is absent and several variables
may be erased at once.

The hypothesis `μ_{n+2} = 0` is absent as well, and it is worth saying why it is not a
weakening. On paper `m_μ[X_{n+1}]` is *defined* only for `μ` with `μ_{n+2} = 0`
(`HJO.Mac.msymmMem` asks the partition to fit in the alphabet), so the hypothesis is there to make
the left-hand side mean anything. Mathlib's `msymm` is defined for every `μ` and is `0` when `μ`
does not fit, so the identity needs no such side condition.

## Main results

* `Nat.Partition.ofSym_map_of_injective`: pushing a multiset forward along an injection does not
  change the partition of multiplicities it induces.
* `MvPolynomial.killCompl_msymm` (`MvPolynomial.killCompl_msymm`, the case `μ_{n+1} = 0`).
* `MvPolynomial.killCompl_msymm_eq_zero` (`MvPolynomial.killCompl_msymm`, the case `μ_{n+1} ≥ 1`).
* `MvPolynomial.msymm_eq_zero_of_card_lt`: `m_μ` vanishes in an alphabet with fewer variables than
  `μ` has parts.

## References

This file proves `MvPolynomial.killCompl_msymm`, on `HJO.Sym.rowLenSeq`, `HJO.Mac.msymmMem` and
`MvPolynomial.eq_killCompl_castSucc_iff`. Its consumers are `MvPolynomial.killComplComp_bijective`
and `HJO.Mac.killComplComp_macPpoly`, both of which are also proved by other routes
(`HJO/Macdonald/CutRestrict.lean`, `HJO/Macdonald/PpolyCut.lean`).
-/

@[expose] public section

open Finset MvPolynomial

variable {σ τ R : Type*} [CommSemiring R] {f : σ → τ} {d : ℕ}

/-! ### Pushing a multiset forward along an injection -/

namespace Nat.Partition

/-- **An injection of alphabets does not change the multiset of multiplicities.** Pushing
`a : Sym σ d` forward along an injective `f` permutes nothing and merges nothing, so the partition
of `d` it induces is unchanged. Mathlib has this for an `Equiv` (`Nat.Partition.ofSym_map`); the
proof is the same, `Multiset.dedup_map_of_injective` and `Multiset.count_map_eq_count'` being the
two facts about `f` that are used. -/
theorem ofSym_map_of_injective [DecidableEq σ] [DecidableEq τ] (hf : Function.Injective f)
    (a : Sym σ d) : ofSym (Sym.map f a) = ofSym a := by
  refine Nat.Partition.ext ?_
  have h₁ : (ofSym (Sym.map f a)).parts
      = ((Sym.map f a : Multiset τ).dedup.map fun y => (Sym.map f a : Multiset τ).count y) := rfl
  have h₂ : (ofSym a).parts
      = ((a : Multiset σ).dedup.map fun y => (a : Multiset σ).count y) := rfl
  rw [h₁, h₂, Sym.coe_map, Multiset.dedup_map_of_injective hf, Multiset.map_map]
  exact Multiset.map_congr rfl fun x _ => Multiset.count_map_eq_count' f _ hf x

end Nat.Partition

namespace Sym

/-- **A multiset all of whose elements lie in the range of `f` is pushed forward from the small
alphabet.** No injectivity and no nonemptiness: the witness is built by induction on the multiset,
one element at a time, so the empty multiset over an empty `σ` is covered. -/
theorem exists_map_eq {a : Sym τ d} (h : ∀ i ∈ (a : Multiset τ), i ∈ Set.range f) :
    ∃ b : Sym σ d, Sym.map f b = a := by
  obtain ⟨m, hm⟩ : ∃ m : Multiset σ, m.map f = (a : Multiset τ) := by
    generalize (a : Multiset τ) = s at h
    induction s using Multiset.induction with
    | empty => exact ⟨0, rfl⟩
    | cons x s ih =>
      obtain ⟨y, rfl⟩ := h x (Multiset.mem_cons_self _ _)
      obtain ⟨b, hb⟩ := ih fun i hi => h i (Multiset.mem_cons_of_mem hi)
      exact ⟨y ::ₘ b, by rw [Multiset.map_cons, hb]⟩
  exact ⟨⟨m, by rw [← Multiset.card_map f m, hm]; exact a.2⟩, Subtype.ext hm⟩

end Sym

/-! ### Erasing variables in a monomial symmetric polynomial -/

namespace MvPolynomial

/-- The monomial of a multiset pushed forward along `f` is carried by `killCompl hf` to the
monomial of the multiset itself: every variable occurring lies in the range of `f`, where
`killCompl hf` is the inverse of `f`. -/
theorem killCompl_prod_map_X (hf : Function.Injective f) (b : Sym σ d) :
    killCompl (R := R) hf ((Sym.map f b : Multiset τ).map X).prod
      = ((b : Multiset σ).map X).prod := by
  rw [Sym.coe_map, Multiset.map_map, map_multiset_prod, Multiset.map_map]
  exact congrArg _ (Multiset.map_congr rfl fun x _ => killCompl_X hf x)

/-- The monomial of a multiset with an element off the range of `f` is killed: that one variable
goes to `0`, and a product with a zero factor is zero. -/
theorem killCompl_prod_map_X_eq_zero (hf : Function.Injective f) (a : Sym τ d)
    (h : ¬ ∀ i ∈ (a : Multiset τ), i ∈ Set.range f) :
    killCompl (R := R) hf ((a : Multiset τ).map X).prod = 0 := by
  obtain ⟨i, hi, hir⟩ : ∃ i ∈ (a : Multiset τ), i ∉ Set.range f := by
    by_contra hc
    exact h fun i hi => not_not.1 fun hn => hc ⟨i, hi, hn⟩
  rw [map_multiset_prod, Multiset.map_map]
  exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨i, hi, killCompl_X_eq_zero hf hir⟩)

/-- **The case `μ_{n+1} = 0`: erasing variables carries a monomial symmetric
polynomial to the monomial symmetric polynomial of the same index in the smaller alphabet.** At
`σ = Fin n`, `τ = Fin (n + 1)` and `f = Fin.castSucc` this is the identity
`cut_n(m_μ[X_{n+1}]) = m_μ[X_n]`; the condition `μ_{n+1} = 0` is what makes its right-hand side
defined, and is not needed here (see `MvPolynomial.killCompl_msymm_eq_zero` for the other case,
which is this identity together with the vanishing of the right-hand side).

The monomials of `msymm τ R μ` that survive are those indexed by an `a : Sym τ d` with every
element in the range of `f`, i.e. by `a = Sym.map f b` (`Sym.exists_map_eq`), and
`Nat.Partition.ofSym_map_of_injective` says that `b` runs over exactly the index set of
`msymm σ R μ`. -/
@[hjo "lem_mac_msymm_cut"]
theorem killCompl_msymm [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
    (hf : Function.Injective f) (μ : Nat.Partition d) :
    killCompl (R := R) hf (msymm τ R μ) = msymm σ R μ := by
  rw [msymm, msymm, map_sum]
  refine (Finset.sum_of_injOn
    (fun b : {b : Sym σ d // Nat.Partition.ofSym b = μ} =>
      (⟨Sym.map f b.1, (Nat.Partition.ofSym_map_of_injective hf b.1).trans b.2⟩ :
        {a : Sym τ d // Nat.Partition.ofSym a = μ}))
    (fun _ _ _ _ hxy => Subtype.ext (Sym.map_injective hf d (Subtype.ext_iff.mp hxy)))
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_
    (fun b _ => (killCompl_prod_map_X hf b.1).symm)).symm
  intro a _ ha
  refine killCompl_prod_map_X_eq_zero hf a.1 fun hr => ha ?_
  obtain ⟨b, hb⟩ := Sym.exists_map_eq hr
  exact ⟨⟨b, (Nat.Partition.ofSym_map_of_injective hf b).symm.trans (hb ▸ a.2)⟩,
    Finset.mem_coe.2 (Finset.mem_univ _), Subtype.ext hb⟩

/-- **A monomial symmetric polynomial vanishes in an alphabet too small for its index.** The index
set of `msymm σ R μ` consists of the `a : Sym σ d` with `Nat.Partition.ofSym a = μ`, and such an `a`
has at most `#σ` distinct elements (`Nat.Partition.parts_card_le`); so for
`#σ < μ.parts.card` the sum is empty. In the sequence indexing this is the statement that
`m_μ[X_n] = 0` when `μ_{n+1} ≥ 1`. -/
theorem msymm_eq_zero_of_card_lt [Fintype σ] [DecidableEq σ] {μ : Nat.Partition d}
    (h : Fintype.card σ < μ.parts.card) : msymm σ R μ = 0 := by
  rw [msymm]
  refine Finset.sum_eq_zero fun s _ => absurd ?_ (not_le.2 h)
  exact s.2 ▸ Nat.Partition.parts_card_le s.1

/-- **`MvPolynomial.killCompl_msymm`, the case `μ_{n+1} ≥ 1`: erasing variables kills a monomial
symmetric polynomial whose index does not fit in the smaller alphabet.** At `σ = Fin n`,
`τ = Fin (n + 1)` and `f = Fin.castSucc` the hypothesis `n < μ.parts.card` is `μ_{n+1} ≥ 1`, and
the conclusion is `cut_n(m_μ[X_{n+1}]) = 0`.

The usual argument is that no rearrangement of `(μ_1, …, μ_{n+1})` has a zero entry, so every
monomial is killed. Here it is the same fact read on the other side: the image is `msymm σ R μ` by
`MvPolynomial.killCompl_msymm`, and that is `0` because no multiset over `σ` has `μ.parts.card`
distinct elements. -/
@[hjo "lem_mac_msymm_cut"]
theorem killCompl_msymm_eq_zero [Fintype σ] [Fintype τ] [DecidableEq τ]
    (hf : Function.Injective f) {μ : Nat.Partition d} (h : Fintype.card σ < μ.parts.card) :
    killCompl (R := R) hf (msymm τ R μ) = 0 := by
  classical
  exact (killCompl_msymm hf μ).trans (msymm_eq_zero_of_card_lt h)

end MvPolynomial
