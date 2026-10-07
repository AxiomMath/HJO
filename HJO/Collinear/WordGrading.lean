/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.IndexShift
public import HJO.Collinear.WordMap
public meta import HJO.Attr

/-! # The length grading of the free algebra on the basic operators

`HJO/Collinear/IndexShift.lean` builds the free `L`-algebra `F = FreeAlgebra L ℕ` on the
symbols `x_0, x_1, …`, the map `π` with `π(x_k) = D_k`, the raise `σ` with `σ(x_k) = x_{k+1}`, and
the descent of `σ` to the operator algebra given that `ker π` is `σ`-stable — the predicate
`HJO.Sym.RaiseStableKernel`. It deliberately does *not* build the grading of `F` by word length,
and says so: the route to `σ`-stability runs through the homogeneous pieces, and the
grading is what connects `π` to the coefficient families of
`HJO/Collinear/WordMap.lean`.

This file builds it. The element of `F` named by a family `c : (Fin k → ℕ) →₀ L` of coefficients
on the words of length `k` is `freeWordElem L k c`, and the two compatibilities that
are usually asserted in passing are proved here:

* `π` carries the element named by `c` to the operator `V_c` it names
  (`dopFreeHom_freeWordElem`), and
* `σ` preserves each homogeneous piece and carries `c` to the raised family `c⁺`
  (`freeIndexRaise_freeWordElem`).

Together with the decomposition `exists_sum_freeWordElem` — every element of `F` is a finite sum
of homogeneous ones, which is the `F = ⨁_k F_k` — this reduces `RaiseStableKernel` to
two statements *about coefficient families only*, with no free algebra left in them:
`raiseStableKernel_of_dopWordOperator`.

## Main definitions

* `HJO.Sym.freeWord`: the word `x_{a_{k-1}} ⋯ x_{a_0}` of a tuple of indices, the rightmost factor
  carrying the first index, as in `dopWordOperator`.
* `HJO.Sym.freeWordElem`: the element of `F` named by a coefficient family on words of one length,
  as a linear map in the family. Its range is the `F_k`.

## Main statements

* `HJO.Sym.dopFreeHom_freeWordElem`: `π` restricted to `F_k` is `dopWordOperator q u k`.
* `HJO.Sym.freeIndexRaise_freeWordElem`: `σ` restricted to `F_k` is `dopWordRaise L k`.
* `HJO.Sym.iSup_range_freeWordElem`: the homogeneous pieces span `F`.
* `HJO.Sym.exists_sum_freeWordElem`: every element of `F` is a finite sum of homogeneous ones.
* `HJO.Sym.raiseStableKernel_of_dopWordOperator`: `RaiseStableKernel q u` follows from the two
  BGLX statements about coefficient families — that a sum over distinct lengths vanishes only if
  each length does, and that raising every index preserves vanishing.

## Implementation notes

**What the rest of the argument needs.** The two hypotheses of
`raiseStableKernel_of_dopWordOperator` are the forward halves of
`HJO.Sym.sum_dopWordOperator_eq_zero_iff` and `HJO.Sym.dopWordOperator_dopWordRaise_eq_zero_iff`,
stated in the vocabulary of `WordMap.lean` and nothing else. Both are consequences of the BGLX
vanishing criterion (`HJO.Bglx.isVanishingCriterion`, BGLX Theorem 2.1), whose statement needs
vocabulary this file does not use: the expansion of the kernel factor as a formal sum, the
exponential alphabet, the plethystic displacement in `k` variables at once and the
Stanton--Stembridge pairing. The criterion is proved in `HJO/Collinear/ExpPairingSeparating.lean`
and the two family statements in `HJO/Collinear/RaiseKernel.lean`; this file is the free-algebra
side of `HJO.Bglx.exists_isIndexShift_param`.

**The grading is built as a span, not as a `GradedAlgebra`.** Only two things are wanted of it —
that the pieces span and that each piece is the image of a linear map with the two
compatibilities above — and a `DirectSum` decomposition would have to carry internal directness,
which nothing here uses: `raiseStableKernel_of_dopWordOperator` splits its element into *some*
finite sum of homogeneous pieces and applies the length-split hypothesis to it, and the
hypothesis is insensitive to whether the decomposition is unique. That the pieces span is proved
from `Algebra.adjoin_eq_span`, the words being the multiplicative closure of the generators, and
`exists_freeWord_of_mem_closure` is the observation that an element of that closure is a single
word rather than a combination of them.

`freeWord` and `freeWordElem` need only `Field L`, matching `freeIndexRaise`; `Algebra ℚ L` enters
only where `dopWordOperator` and `Dop` do.
-/

@[expose] public section

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The words and the homogeneous pieces -/

/-- The word `x_{a_{k-1}} ⋯ x_{a_0}` of a tuple `a : Fin k → ℕ` of indices in the free algebra,
the rightmost factor carrying the first index, as in `dopWordOperator`. -/
noncomputable def freeWord (L : Type*) [Field L] {k : ℕ} (a : Fin k → ℕ) : FreeAlgebra L ℕ :=
  (List.ofFn fun i => FreeAlgebra.ι L (a i)).reverse.prod

/-- The element of the free algebra named by a coefficient family on the words of length `k`:
`∑ a, c a • x_{a_{k-1}} ⋯ x_{a_0}`. Its range is the homogeneous piece `F_k`. -/
noncomputable def freeWordElem (L : Type*) [Field L] (k : ℕ) :
    ((Fin k → ℕ) →₀ L) →ₗ[L] FreeAlgebra L ℕ :=
  Finsupp.linearCombination L fun a => freeWord L a

omit [Algebra ℚ L] in
@[simp] theorem freeWordElem_single {k : ℕ} (a : Fin k → ℕ) (r : L) :
    freeWordElem L k (Finsupp.single a r) = r • freeWord L a := by
  simp [freeWordElem]

/-! ### The two compatibilities -/

theorem dopFreeHom_freeWordElem (q u : L) (k : ℕ) (c : (Fin k → ℕ) →₀ L) :
    dopFreeHom q u (freeWordElem L k c) = dopWordOperator q u k c := by
  rw [freeWordElem, dopWordOperator, Finsupp.linearCombination_apply,
    Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul]
  congr 1
  simp [freeWord, map_list_prod, List.map_reverse, List.map_ofFn, Function.comp_def]

omit [Algebra ℚ L] in
theorem freeIndexRaise_freeWordElem (k : ℕ) (c : (Fin k → ℕ) →₀ L) :
    freeIndexRaise L (freeWordElem L k c) = freeWordElem L k (dopWordRaise L k c) := by
  rw [freeWordElem, dopWordRaise, Finsupp.lmapDomain_apply,
    Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply,
    Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul]
  congr 1
  simp [freeWord, map_list_prod, List.map_reverse, List.map_ofFn, Function.comp_def]

/-! ### The pieces span -/

omit [Algebra ℚ L] in
/-- Concatenating tuples multiplies the words, in the order `dopWordOperator` reads them. -/
theorem freeWord_append {m n : ℕ} (b : Fin m → ℕ) (a : Fin n → ℕ) :
    freeWord L (Fin.append b a) = freeWord L a * freeWord L b := by
  have h : (List.ofFn fun i => FreeAlgebra.ι L (Fin.append b a i))
      = (List.ofFn fun i => FreeAlgebra.ι L (b i))
          ++ (List.ofFn fun i => FreeAlgebra.ι L (a i)) := by
    simp only [← Function.comp_def, ← List.map_ofFn, List.ofFn_fin_append, List.map_append]
  rw [freeWord, h, List.reverse_append, List.prod_append, freeWord, freeWord]

omit [Algebra ℚ L] in
theorem freeWord_mem_iSup {k : ℕ} (a : Fin k → ℕ) :
    freeWord L a ∈ ⨆ j : ℕ, LinearMap.range (freeWordElem L j) := by
  refine Submodule.mem_iSup_of_mem k ⟨Finsupp.single a 1, ?_⟩
  rw [freeWordElem_single, one_smul]

omit [Algebra ℚ L] in
/-- An element of the multiplicative closure of the generators is a single word, not a
combination of words. -/
theorem exists_freeWord_of_mem_closure {y : FreeAlgebra L ℕ}
    (hy : y ∈ Submonoid.closure (Set.range (FreeAlgebra.ι L (X := ℕ)))) :
    ∃ (k : ℕ) (a : Fin k → ℕ), freeWord L a = y := by
  induction hy using Submonoid.closure_induction with
  | one => exact ⟨0, fun _ => 0, by simp [freeWord]⟩
  | mem x hx =>
      obtain ⟨n, rfl⟩ := hx
      exact ⟨1, fun _ => n, by simp [freeWord]⟩
  | mul x y hx hy ihx ihy =>
      obtain ⟨kx, ax, hax⟩ := ihx
      obtain ⟨ky, ay, hay⟩ := ihy
      exact ⟨ky + kx, Fin.append ay ax, by rw [freeWord_append, hax, hay]⟩

omit [Algebra ℚ L] in
/-- **The homogeneous pieces span the free algebra**, which is
`F = ⨁_{k ≥ 0} F_k` in the only form used below. -/
theorem iSup_range_freeWordElem :
    (⨆ k : ℕ, LinearMap.range (freeWordElem L k)) = ⊤ := by
  have hid : FreeAlgebra.lift L (FreeAlgebra.ι L (X := ℕ)) = AlgHom.id L (FreeAlgebra L ℕ) := by
    simpa using FreeAlgebra.lift_comp_ι (AlgHom.id L (FreeAlgebra L ℕ))
  have htop : Algebra.adjoin L (Set.range (FreeAlgebra.ι L (X := ℕ))) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_freeAlgebra_lift, hid]
    ext x
    simp
  refine top_le_iff.mp ?_
  have h1 : (⊤ : Submodule L (FreeAlgebra L ℕ))
      = Submodule.span L
          (Submonoid.closure (Set.range (FreeAlgebra.ι L (X := ℕ))) : Set (FreeAlgebra L ℕ)) := by
    rw [← Algebra.adjoin_eq_span, htop]
    rfl
  rw [h1, Submodule.span_le]
  intro y hy
  obtain ⟨k, a, rfl⟩ := exists_freeWord_of_mem_closure hy
  exact freeWord_mem_iSup a

omit [Algebra ℚ L] in
/-- **Every element of the free algebra is a finite sum of homogeneous ones.** The family `c` is
total, vanishing off the finite set `s` of lengths that occur. -/
theorem exists_sum_freeWordElem (V : FreeAlgebra L ℕ) :
    ∃ (s : Finset ℕ) (c : ∀ k : ℕ, ((Fin k → ℕ) →₀ L)),
      (∀ k ∉ s, c k = 0) ∧ V = ∑ k ∈ s, freeWordElem L k (c k) := by
  have hV : V ∈ ⨆ k : ℕ, LinearMap.range (freeWordElem L k) := by
    rw [iSup_range_freeWordElem]; trivial
  refine Submodule.iSup_induction
    (motive := fun W => ∃ (s : Finset ℕ) (c : ∀ k : ℕ, ((Fin k → ℕ) →₀ L)),
      (∀ k ∉ s, c k = 0) ∧ W = ∑ k ∈ s, freeWordElem L k (c k))
    (fun k : ℕ => LinearMap.range (freeWordElem L k)) hV ?_ ?_ ?_
  · rintro i x ⟨ci, rfl⟩
    refine ⟨{i}, Function.update (fun k => (0 : (Fin k → ℕ) →₀ L)) i ci, ?_, ?_⟩
    · intro k hk
      simp only [Finset.mem_singleton] at hk
      rw [Function.update_of_ne hk]
    · rw [Finset.sum_singleton, Function.update_self]
  · exact ⟨∅, fun _ => 0, by simp, by simp⟩
  · rintro x y ⟨s₁, c₁, hc₁, hx₁⟩ ⟨s₂, c₂, hc₂, hy₂⟩
    refine ⟨s₁ ∪ s₂, fun k => c₁ k + c₂ k, ?_, ?_⟩
    · intro k hk
      rw [Finset.mem_union, not_or] at hk
      simp only [hc₁ k hk.1, hc₂ k hk.2, add_zero]
    · have e₁ : ∑ k ∈ s₁ ∪ s₂, freeWordElem L k (c₁ k) = x := by
        rw [hx₁]
        refine (Finset.sum_subset Finset.subset_union_left ?_).symm
        intro k _ hk
        rw [hc₁ k hk, map_zero]
      have e₂ : ∑ k ∈ s₁ ∪ s₂, freeWordElem L k (c₂ k) = y := by
        rw [hy₂]
        refine (Finset.sum_subset Finset.subset_union_right ?_).symm
        intro k _ hk
        rw [hc₂ k hk, map_zero]
      rw [← e₁, ← e₂, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => (map_add _ _ _).symm

/-! ### What `RaiseStableKernel` reduces to -/

/-- **`ker π` is `σ`-stable as soon as the two BGLX statements about coefficient families hold.**
The hypotheses are the forward halves of `HJO.Sym.sum_dopWordOperator_eq_zero_iff` — a sum of the
operators of families of distinct word lengths vanishes only if each summand does — and of
`HJO.Sym.dopWordOperator_dopWordRaise_eq_zero_iff` — raising every index preserves vanishing. Both
speak only of `dopWordOperator` and `dopWordRaise`, so this discharges the whole free-algebra side
of `HJO.Bglx.exists_isIndexShift_param`: with these two in hand, `exists_isIndexShift` produces an
index shift. -/
theorem raiseStableKernel_of_dopWordOperator {q u : L}
    (hsplit : ∀ (s : Finset ℕ) (c : ∀ k : ℕ, ((Fin k → ℕ) →₀ L)),
      ∑ k ∈ s, dopWordOperator q u k (c k) = 0 → ∀ k ∈ s, dopWordOperator q u k (c k) = 0)
    (hraise : ∀ (k : ℕ) (c : (Fin k → ℕ) →₀ L),
      dopWordOperator q u k c = 0 → dopWordOperator q u k (dopWordRaise L k c) = 0) :
    RaiseStableKernel q u := by
  intro V hV
  obtain ⟨s, c, -, rfl⟩ := exists_sum_freeWordElem V
  rw [map_sum] at hV
  simp only [dopFreeHom_freeWordElem] at hV
  rw [map_sum, map_sum]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [freeIndexRaise_freeWordElem, dopFreeHom_freeWordElem]
  exact hraise k (c k) (hsplit s c hV k hk)

end HJO.Sym
