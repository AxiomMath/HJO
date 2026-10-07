/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.SuperSchur
public meta import HJO.Attr

/-! # The super fundamental expansion of a super Schur series

The super Schur series of a Young diagram is the sum of the super fundamentals at the descent sets
of the standard tableaux of that diagram: `sch̃(D) = ∑_{S ∈ SYT(D)} F̃_{#D, Des(S)}`. This is the
super analogue of Gessel's expansion of a Schur function, and it is the bijection
`HJO.Sym.superTableauOfPair_bijective` summed.

## Main definitions

* `HJO.Sym.boundedStdPairs`: the admissible pairs whose word has letters of bounded absolute value,
  the finite index set on which both sides of the expansion are read at one monomial.

## Main results

* `HJO.Sym.superSchurSeries_eq_sum_superFundamental`.

## Implementation notes

*The `∑_{S ∈ SYT(D)}` is a `Finset` sum over the type `HJO.Sym.SYT`.* That type is
finite — a standard tableau is determined by its values on the cells and those values are below the
number of cells, which is `HJO.Sym.instFiniteSYT` — so it carries a `Fintype` and the sum is the
honest finite one. Nothing of the summability layer is needed on the outer sum; it is needed on each
summand, both `sch̃(D)` and `F̃_{n,S}` being `HJO.Sym.summableSum` of an infinite family.

*The identity is proved one coefficient at a time, and the two sides meet on
`HJO.Sym.boundedStdPairs`.* Neither side is a finite sum of nonzero terms, so the bijection
`HJO.Sym.superTableauOfPair_bijective` cannot be applied to it directly; at a fixed monomial `x^d`,
however, both sides are `Finset` sums, and the finite index sets are matched by that bijection cut
down to the tableaux and the words whose letters have absolute value in the support of `d`. Those
are the only ones reaching `x^d`, by `HJO.Sym.prod_superVar`: a product of super variables is one
monomial at the exponent vector of its absolute values. The matching is carried by the *canonical*
pair of a super tableau — `HJO.Sym.superStdTableau` and `HJO.Sym.superStdWord`, which is a total
map, no admissibility proof being needed to write it down — rather than by the inverse of the
abstract bijection, which is what makes it usable as the index map of `Finset.sum_bij`.

*The `z_T = z_v` is `HJO.Sym.superTableauMonomial_superTableauOfPair`*: the cells and
the positions are matched by `S`, which on a standard tableau is a bijection from the cells onto the
values, so the two products have the same factors.

*The `n ≥ 1` is dropped.* At `n = 0` the diagram is empty, each side is `1` — the empty
diagram has one super tableau and one standard tableau, and the empty word is super ascending — and
no step of the proof uses positivity.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle
conjecture*, J. Amer. Math. Soc.
**31** (2018) 661--697, Section 3.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### The standard tableaux of a diagram are finite in number -/

/-- **The standard tableaux of a diagram are finite in number**: a standard tableau is determined by
its values on the cells, and those values lie below the number of cells, so `SYT(D)` injects into
the maps from the cells to `Fin #D`. This is what makes the sum over `SYT(D)` a finite
sum. -/
instance instFiniteSYT (μ : YoungDiagram) : Finite (SYT μ) := by
  refine Finite.of_injective (β := ↥μ.cells → Fin μ.card)
    (fun S c => ⟨S.1 (c : ℕ × ℕ).1 (c : ℕ × ℕ).2, S.2.lt_card c.2⟩) fun S S' h => ?_
  refine Subtype.ext (SemistandardYoungTableau.ext fun i j => ?_)
  by_cases hc : ((i, j) : ℕ × ℕ) ∈ μ
  · exact congrArg Fin.val (congrFun h ⟨(i, j), by simpa using hc⟩)
  · rw [S.1.zeros hc, S'.1.zeros hc]

/-- The standard tableaux of a diagram as a finite type, which is what the sum over
`SYT(D)` is taken over. It is `Fintype.ofFinite` at `HJO.Sym.instFiniteSYT`: the enumeration is not
needed, only the finiteness. -/
noncomputable instance instFintypeSYT (μ : YoungDiagram) : Fintype (SYT μ) :=
  Fintype.ofFinite _

/-! ### The letters that reach a monomial -/

variable {K : Type*} [CommRing K]

/-- **A super word reaching a monomial has every absolute value in the support of that monomial**:
`z_v` is one monomial, at the exponent vector of the absolute values, by
`HJO.Sym.prod_superVar`. -/
theorem absVal_mem_support_of_coeff_superMonomial {n : ℕ} (q : K) (v : Fin n → SuperLetter)
    {d : ℕ →₀ ℕ} (h : MvPowerSeries.coeff d (superMonomial K q v) ≠ 0) (i : Fin n) :
    (v i).absVal ∈ d.support := by
  rw [superMonomial, coeff_prod_superVar] at h
  by_cases hd : d = ∑ j : Fin n, Finsupp.single (v j).absVal 1
  · rw [hd]
    exact absVal_mem_support_sum univ v (mem_univ i)
  · exact absurd (ite_eq_right hd) h

/-- **A super tableau reaching a monomial has every absolute value in the support of that
monomial**, for the same reason: `z_T` is one monomial. -/
theorem absVal_mem_support_of_coeff_superTableauMonomial {μ : YoungDiagram} (q : K)
    (T : SuperYoungTableau μ) {d : ℕ →₀ ℕ}
    (h : MvPowerSeries.coeff d (superTableauMonomial K q T) ≠ 0) {c : ℕ × ℕ} (hc : c ∈ μ.cells) :
    (T c.1 c.2).absVal ∈ d.support := by
  rw [superTableauMonomial, coeff_prod_superVar] at h
  by_cases hd : d = ∑ e ∈ μ.cells, Finsupp.single (T e.1 e.2).absVal 1
  · rw [hd]
    exact absVal_mem_support_sum μ.cells (fun e => T e.1 e.2) hc
  · exact absurd (ite_eq_right hd) h

/-- **Only finitely many super tableaux take their letters among those of bounded absolute value**:
a super tableau is determined by its values on the cells, and there are two letters of each absolute
value. This is the finite set of tableaux the super Schur series is read on at one monomial. -/
theorem finite_superYoungTableau_absVal_mem (μ : YoungDiagram) (u : Finset ℕ) :
    {T : SuperYoungTableau μ | ∀ c ∈ μ.cells, (T c.1 c.2).absVal ∈ u}.Finite := by
  have hinj : Function.Injective
      fun (T : SuperYoungTableau μ) => fun c : ↥μ.cells => T (c : ℕ × ℕ).1 (c : ℕ × ℕ).2 := by
    intro T T' h
    refine SuperYoungTableau.ext fun i j => ?_
    by_cases hc : ((i, j) : ℕ × ℕ) ∈ μ
    · exact congrFun h ⟨(i, j), by simpa using hc⟩
    · rw [T.outside hc, T'.outside hc]
  refine Set.Finite.of_finite_image ?_ hinj.injOn
  refine Set.Finite.subset (Set.Finite.pi fun _ : ↥μ.cells => finite_absVal_mem u) ?_
  rintro g ⟨T, hT, rfl⟩
  exact fun c _ => hT (c : ℕ × ℕ) c.2

/-! ### The monomial of an admissible pair is the monomial of its word -/

/-- **The `z_T = z_v`**: the monomial of the filling `c ↦ v_{S(c)}` of an admissible
pair is the monomial of the word. The two products have the same factors, `S` being a bijection from
the cells onto the positions. -/
theorem superTableauMonomial_superTableauOfPair {μ : YoungDiagram} (q : K) (p : SuperStdPair μ) :
    superTableauMonomial K q (superTableauOfPair p) = superMonomial K q p.1.2 := by
  rw [superTableauMonomial, superMonomial]
  refine Finset.prod_bij (fun c hc => (⟨p.1.1 c.1 c.2, p.2.1.lt_card hc⟩ : Fin μ.card))
    (fun c _ => mem_univ _) (fun c hc c' hc' h => ?_) (fun i _ => ?_) fun c hc => ?_
  · exact p.2.1.injOn (by simpa using hc) (by simpa using hc') (congrArg Fin.val h)
  · obtain ⟨c, hc, hcv⟩ := p.2.1.exists_eq i.isLt
    exact ⟨c, hc, Fin.ext hcv⟩
  · rw [show ⇑(superTableauOfPair p) = pairEntry p.1.1 p.1.2 from rfl, pairEntry_of_mem p.2.1 hc]

/-- **The monomial of a super tableau is the monomial of its canonical word**: the case of
`HJO.Sym.superTableauMonomial_superTableauOfPair` at the canonical pair, which is the form the
expansion uses. -/
theorem superTableauMonomial_eq_superMonomial_superStdWord {μ : YoungDiagram} (q : K)
    (T : SuperYoungTableau μ) :
    superTableauMonomial K q T = superMonomial K q (superStdWord T) :=
  (congrArg (superTableauMonomial K q) (superTableauOfPair_canonical T
    (isStandard_superStdTableau T) (isSuperAdmissibleWord_superStdWord T)).symm).trans
      (superTableauMonomial_superTableauOfPair q _)

/-! ### The admissible pairs reaching one monomial -/

/-- **The admissible pairs whose word has letters of bounded absolute value**: the pairs `(S, v)` of
`HJO.Sym.superTableauOfPair_bijective` with `S ∈ SYT(D)` and every letter of `v` of absolute value
in `u`. At `u` the support of a monomial this is the finite index set both sides of the expansion
are read on at that monomial: no other pair contributes there. -/
noncomputable def boundedStdPairs (μ : YoungDiagram) (u : Finset ℕ) :
    Finset (SYT μ × (Fin μ.card → SuperLetter)) :=
  {p ∈ (univ : Finset (SYT μ)) ×ˢ Fintype.piFinset fun _ : Fin μ.card => letterFinset u |
    IsSuperAscendingWord μ.card (sytDescentSet p.1.1) p.2}

/-- Membership in `HJO.Sym.boundedStdPairs`: the letters are bounded and the pair is admissible. -/
theorem mem_boundedStdPairs {μ : YoungDiagram} {u : Finset ℕ}
    {p : SYT μ × (Fin μ.card → SuperLetter)} :
    p ∈ boundedStdPairs μ u ↔ (∀ i, (p.2 i).absVal ∈ u) ∧
      IsSuperAscendingWord μ.card (sytDescentSet p.1.1) p.2 := by
  rw [boundedStdPairs, mem_filter, mem_product]
  simp only [mem_univ, true_and, Fintype.mem_piFinset, mem_letterFinset]

/-! ### The two coefficient computations -/

/-- **The coefficients of the super Schur series, read on the admissible pairs**: the tableaux
reaching a monomial are the fillings of the admissible pairs whose word has letters of absolute
value in the support of that monomial, and the monomial of such a filling is the monomial of its
word. This is `HJO.Sym.superTableauOfPair_bijective` cut down to one coefficient. -/
theorem coeff_superSchurSeries_eq_sum (q : K) (μ : YoungDiagram) (d : ℕ →₀ ℕ) :
    MvPowerSeries.coeff d (superSchurSeries K q μ)
      = ∑ p ∈ boundedStdPairs μ d.support, MvPowerSeries.coeff d (superMonomial K q p.2) := by
  have hfin := finite_superYoungTableau_absVal_mem μ d.support
  rw [superSchurSeries]
  refine Eq.trans (coeff_summableSum_eq_sum (s := hfin.toFinset) fun T hT => ?_) ?_
  · exact hfin.mem_toFinset.2 fun c hc =>
      absVal_mem_support_of_coeff_superTableauMonomial q T hT hc
  refine Finset.sum_bij (fun T _ =>
    ((⟨superStdTableau T, isStandard_superStdTableau T⟩ : SYT μ), superStdWord T))
      (fun T hT => ?_) (fun T hT T' hT' h => ?_) (fun p hp => ?_) fun T _ => ?_
  · refine mem_boundedStdPairs.2 ⟨fun i => ?_, isSuperAdmissibleWord_superStdWord T⟩
    exact hfin.mem_toFinset.1 hT _ (superStdCell_mem T i)
  · have h1 : superStdTableau T = superStdTableau T' :=
      congrArg Subtype.val (congrArg Prod.fst h)
    have h2 : superStdWord T = superStdWord T' := congrArg Prod.snd h
    rw [← superTableauOfPair_canonical T (isStandard_superStdTableau T)
      (isSuperAdmissibleWord_superStdWord T)]
    rw [← superTableauOfPair_canonical T' (isStandard_superStdTableau T')
      (isSuperAdmissibleWord_superStdWord T')]
    exact congrArg superTableauOfPair (Subtype.ext (Prod.ext h1 h2))
  · obtain ⟨hletters, hadm⟩ := mem_boundedStdPairs.1 hp
    refine ⟨superTableauOfPair ⟨(p.1.1, p.2), p.1.2, hadm⟩, hfin.mem_toFinset.2 fun c hc => ?_,
      Prod.ext (Subtype.ext (superStdTableau_superTableauOfPair _))
        (superStdWord_superTableauOfPair _)⟩
    rw [show ⇑(superTableauOfPair ⟨(p.1.1, p.2), p.1.2, hadm⟩) = pairEntry p.1.1 p.2 from rfl,
      pairEntry_of_mem p.1.2 hc]
    exact hletters _
  · rw [superTableauMonomial_eq_superMonomial_superStdWord]

/-- **The coefficients of the sum of super fundamentals, read on the admissible pairs**: the words
reaching a monomial have their letters of absolute value in its support, so the sum over `SYT(D)` of
the coefficients is the sum over the admissible pairs of the coefficient of the monomial of the
word. -/
theorem coeff_sum_superFundamental_eq_sum (q : K) (μ : YoungDiagram) (d : ℕ →₀ ℕ) :
    MvPowerSeries.coeff d (∑ S : SYT μ, superFundamental K q μ.card (sytDescentSet S.1))
      = ∑ p ∈ boundedStdPairs μ d.support, MvPowerSeries.coeff d (superMonomial K q p.2) := by
  have hstep : ∀ S : SYT μ,
      MvPowerSeries.coeff d (superFundamental K q μ.card (sytDescentSet S.1))
        = ∑ v ∈ Fintype.piFinset fun _ : Fin μ.card => letterFinset d.support,
            if IsSuperAscendingWord μ.card (sytDescentSet S.1) v then
              MvPowerSeries.coeff d (superMonomial K q v) else 0 := by
    intro S
    have hs : ∀ v : Fin μ.card → SuperLetter, MvPowerSeries.coeff d
        (if IsSuperAscendingWord μ.card (sytDescentSet S.1) v then superMonomial K q v
          else 0) ≠ 0 → v ∈ Fintype.piFinset fun _ : Fin μ.card => letterFinset d.support := by
      intro v hv
      rw [Fintype.mem_piFinset]
      intro i
      rw [mem_letterFinset]
      by_cases hadm : IsSuperAscendingWord μ.card (sytDescentSet S.1) v
      · rw [ite_eq_left hadm] at hv
        exact absVal_mem_support_of_coeff_superMonomial q v hv i
      · rw [ite_eq_right hadm, map_zero] at hv
        exact absurd rfl hv
    rw [coeff_superFundamental_eq_sum q μ.card (sytDescentSet S.1) hs]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs with h
    · rfl
    · exact map_zero _
  calc MvPowerSeries.coeff d (∑ S : SYT μ, superFundamental K q μ.card (sytDescentSet S.1))
      = ∑ S : SYT μ, MvPowerSeries.coeff d (superFundamental K q μ.card (sytDescentSet S.1)) :=
        map_sum _ _ _
    _ = ∑ S : SYT μ, ∑ v ∈ Fintype.piFinset fun _ : Fin μ.card => letterFinset d.support,
          if IsSuperAscendingWord μ.card (sytDescentSet S.1) v then
            MvPowerSeries.coeff d (superMonomial K q v) else 0 :=
        Finset.sum_congr rfl fun S _ => hstep S
    _ = ∑ p ∈ (univ : Finset (SYT μ)) ×ˢ Fintype.piFinset fun _ : Fin μ.card =>
            letterFinset d.support,
          if IsSuperAscendingWord μ.card (sytDescentSet p.1.1) p.2 then
            MvPowerSeries.coeff d (superMonomial K q p.2) else 0 :=
        (Finset.sum_product' ..).symm
    _ = ∑ p ∈ boundedStdPairs μ d.support, MvPowerSeries.coeff d (superMonomial K q p.2) := by
        rw [boundedStdPairs, Finset.sum_filter]

/-! ### The expansion -/

/-- **The super fundamental expansion of a super Schur series.**
`sch̃(D) = ∑_{S ∈ SYT(D)} F̃_{n, Des(S)}` with `n = #D`.

This is `HJO.Sym.superTableauOfPair_bijective` summed: the super tableaux of `D` are the fillings
`c ↦ v_{S(c)}` of the admissible pairs `(S, v)`, and such a filling has `z_T = z_v` because `S` is
a bijection from the cells onto the positions, so grouping the tableaux by `S` turns `sch̃(D)` into
the sum over `S ∈ SYT(D)` of the sum of `z_v` over the words that are super ascending for `Des(S)`,
which is `F̃_{n,Des(S)}`. Both sides being sums of infinite families, the grouping is carried out at
a fixed monomial, where each side is the finite sum over the admissible pairs whose word has letters
of absolute value in the support of that monomial.

The `n ≥ 1` is not needed: at `n = 0` both sides are `1`. -/
@[hjo "lem_cm_super_schur_gessel"]
theorem superSchurSeries_eq_sum_superFundamental (q : K) (μ : YoungDiagram) :
    superSchurSeries K q μ = ∑ S : SYT μ, superFundamental K q μ.card (sytDescentSet S.1) :=
  MvPowerSeries.ext fun d =>
    (coeff_superSchurSeries_eq_sum q μ d).trans (coeff_sum_superFundamental_eq_sum q μ d).symm

end HJO.Sym
