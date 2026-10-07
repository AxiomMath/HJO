/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.ZRing
public meta import HJO.Attr

/-! # The alphabet-graded subring and its relabellings

`HJO.CarlssonMellit.ZRing` builds the set `Z^{(k+1)}` of finite sums of alphabet-graded series
and the relabelling `ŝ_ρ` of the merged alphabet, and proves the two facts that make the grading a
grading. This file proves the ring-theoretic half: `Z^{(k+1)}` is a subring of
`P°_{k+1}`, the relabellings preserve each graded piece, they compose, and each is a ring
automorphism of `Z^{(k+1)}` fixing the lower coefficient field, with inverse the relabelling along
the inverse permutation. The interchange `ŝ_m` of two adjacent letters is the transposition case.

## Main definitions

* `HJO.Sym.zSubring`: `Z^{(k+1)}` as a `Subring` of `P°_{k+1}`.
* `HJO.Sym.zPoly`: the polynomial in `y_{k+1}` over `𝕂(y₁, …, y_k)` that a coefficient of a member
  of `Z^{(k+1)}` is, so that the merged coefficients `HJO.Sym.zCoeff` are *its* coefficients.
* `HJO.Sym.zLetter`, `HJO.Sym.zSwapEquiv`, `HJO.Sym.zSwap`: the letter of the merged alphabet at a
  given offset from the level, the transposition interchanging two adjacent letters, and the
  resulting operator `ŝ_m` on `P°_{k+1}`.
* `HJO.Sym.zPermEquiv`: `ŝ_ρ` as a ring automorphism of `Z^{(k+1)}`.

## Main results

* `HJO.Sym.zPerm_mem_zGraded` and `HJO.Sym.zPerm_image_zGraded_subset`:
  `ŝ_ρ(Z^{(k+1)}_d) ⊆ Z^{(k+1)}_d`.
* `HJO.Sym.zCoeff_zPerm`: the merged coefficients of `ŝ_ρ G` are those of `G` read at the relabelled
  exponent vectors. This is the computational content of everything below it.
* `HJO.Sym.zPerm_zPerm`: `ŝ_ρ ∘ ŝ_{ρ'} = ŝ_{ρρ'}` on `Z^{(k+1)}`.
* `HJO.Sym.zCoeff_mul`: the merged coefficients of a product are the convolution of the merged
  coefficients, which is what makes `ŝ_ρ` multiplicative.
* `HJO.Sym.zPerm_mul_of_mem_zRing`, `HJO.Sym.zPerm_one`, `HJO.Sym.zPerm_zPerm_symm`: `ŝ_ρ` is a ring
  automorphism of `Z^{(k+1)}` with inverse `ŝ_{ρ^{-1}}`.

## Implementation notes

*The level and the conventions are those of `HJO.CarlssonMellit.SeriesGrading` and
`HJO.CarlssonMellit.ZRing`* and are not revisited: the level `k ≥ 1` is `k + 1`
here, its `y_k` is `HJO.Sym.yFrac K (Fin.last k)`, its coefficient field `𝕂(y₁, …, y_{k-1})` is
`HJO.Sym.AuxFrac K k` included by `HJO.Sym.auxFracCastSucc`, and a `y`-exponent is always a witness
`b` to `b + |α| = d` and never `d - |α|`.

*`Z^{(k+1)}` is packaged as a `Subring` and not as a `Subalgebra`.* A subring asks nothing of the
ambient scalars, so the packaging is available where a `Subalgebra` would not be: there is no
`Algebra (AuxFrac K k) (AuxAlphabetSeriesFrac K (k + 1))` instance and deliberately so — see
`HJO.CarlssonMellit.SeriesGrading` — the lower coefficient field acting only through the ring
homomorphism `HJO.Sym.auxFracCastSucc`.

*The "algebra automorphism over `𝕂(y₁, …, y_{k-1})`" is rendered as a ring automorphism
together with the assertion that it fixes that field pointwise*, which is `HJO.Sym.zPerm_C` below.
The two together are exactly base-linearity — `ŝ_ρ(cG) = ŝ_ρ(ι c)ŝ_ρ(G) = ι c · ŝ_ρ(G)` — and they
say it without an `Algebra (AuxFrac K k) (AuxAlphabetSeriesFrac K (k + 1))` instance, which would be
the diamond the grading was set up to avoid: the lower field maps into `Z^{(k+1)}_0` and so *would*
make `Z^{(k+1)}` an algebra over it, but only after choosing between that route and the
`auxFracCastSucc`-scalar action already in use. `HJO.Sym.zPerm_auxFracCastSucc_smul_of_mem_zRing`
of `HJO.CarlssonMellit.ZRing` states the same linearity for that action.

*The merged coefficients are the coefficients of an honest polynomial.* Every statement about
`HJO.Sym.zPerm` is a statement about `HJO.Sym.zCoeff`, and the tool that makes those tractable is
`HJO.Sym.zPoly`: for `G` in `Z^{(k+1)}` the coefficient of `G` at a letter-monomial `x^α` lies in
the range of `HJO.Sym.yFracEval`, and `zPoly K k G α` is the unique polynomial evaluating to it, so
that `zCoeff K k G (α.optionElim b)` *is* its `b`-th coefficient. The merged coefficients therefore
inherit the polynomial API: `HJO.Sym.zCoeff_mul` is `Polynomial.coeff_mul` under
`MvPowerSeries.coeff_mul`, and `HJO.Sym.eq_of_zCoeff_eq` — that a member of `Z^{(k+1)}` is
determined by its merged coefficients — is `Polynomial.ext` under `MvPowerSeries.ext`.

*The offset, not the absolute index, parametrises the interchange.* The interchange `ŝ_m` is indexed
by `m ≥ k`, at the level where the letters are `z^{(k)}_j` for `j ≥ k`; at the level `k + 1` that
reads `m ≥ k + 1` and letters `z^{(k+1)}_j` for `j ≥ k + 1`, so the interchanges are indexed by the
offset `r = m - (k + 1)`, which ranges over all of `ℕ`. `HJO.Sym.zSwap K k r` is the interchange
`ŝ_{k+1+r}`. Carrying the offset rather than `m` keeps `ℕ`-subtraction out of the definition, and
`HJO.Sym.zLetter` — `zLetter 0 = none`, the distinguished letter `y_{k+1}`, and
`zLetter (i + 1) = some i`, the letter `x_{i+1}` — is written by recursion for the same reason. The
fact that the two uses of the symbol `ŝ` do not clash is the disjointness of the ranges `m ≥ k + 1`
and `1 ≤ m ≤ k` and needs nothing here.

*Membership hypotheses, not a definition by cases.* `HJO.Sym.zPerm` is defined on all of `P°_{k+1}`
and is the map only on `Z^{(k+1)}`, so every statement below about composition,
multiplicativity or invertibility carries a membership hypothesis
— they are statements about a map of `Z^{(k+1)}`. `HJO.Sym.zPermEquiv` collects them into a
`RingAut` of the subring, where there is nothing left to hypothesise.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 4. The grading and its relabellings are this library's apparatus rather than
the paper's.
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K] [IsDomain K] {k d e : ℕ}
  {G H : AuxAlphabetSeriesFrac K (k + 1)}

/-! ### Finite sums of graded series -/

/-- A finite sum of members of one graded piece is one: iterated `HJO.Sym.add_mem_zGraded`. -/
theorem sum_mem_zGraded {ι : Type*} {t : Finset ι} {F : ι → AuxAlphabetSeriesFrac K (k + 1)}
    (hF : ∀ i ∈ t, F i ∈ zGraded K k d) : ∑ i ∈ t, F i ∈ zGraded K k d := by
  classical
  induction t using Finset.cons_induction with
  | empty => simpa using zero_mem_zGraded
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact add_mem_zGraded (hF a (Finset.mem_cons_self ..))
      (ih fun i hi => hF i (Finset.mem_cons_of_mem hi))

/-- `Z^{(k+1)}_d` is closed under differences. -/
theorem sub_mem_zGraded (hG : G ∈ zGraded K k d) (hH : H ∈ zGraded K k d) :
    G - H ∈ zGraded K k d := by
  rw [sub_eq_add_neg]
  exact add_mem_zGraded hG (neg_mem_zGraded hH)

/-- The unit series lies in the degree-zero piece: its only nonzero coefficient sits at the empty
letter-monomial, where it is `1 = 1 · y_{k+1}^0`. -/
theorem one_mem_zGraded : (1 : AuxAlphabetSeriesFrac K (k + 1)) ∈ zGraded K k 0 := by
  classical
  refine ⟨fun α b hb => ⟨1, ?_⟩, fun α hα => ?_⟩
  · have hα : α = 0 := Finsupp.degree_eq_zero_iff α |>.1 (by omega)
    have hb : b = 0 := by omega
    rw [hα, hb, MvPowerSeries.coeff_one, ite_eq_left rfl, map_one, pow_zero, mul_one]
  · refine (MvPowerSeries.coeff_one α).trans (ite_eq_right ?_)
    rintro rfl
    simp at hα

/-! ### The alphabet-graded subring -/

/-- `Z^{(k+1)}` contains `0`. -/
theorem zero_mem_zRing : (0 : AuxAlphabetSeriesFrac K (k + 1)) ∈ zRing K k :=
  zGraded_subset_zRing K k 0 zero_mem_zGraded

/-- `Z^{(k+1)}` contains `1`. -/
theorem one_mem_zRing : (1 : AuxAlphabetSeriesFrac K (k + 1)) ∈ zRing K k :=
  zGraded_subset_zRing K k 0 one_mem_zGraded

/-- `Z^{(k+1)}` is closed under addition: add the two decompositions degreewise, over the union of
the two finite sets of degrees they use. -/
theorem add_mem_zRing (hG : G ∈ zRing K k) (hH : H ∈ zRing K k) : G + H ∈ zRing K k := by
  classical
  obtain ⟨s, F, hF, hs, rfl⟩ := hG
  obtain ⟨t, F', hF', ht, rfl⟩ := hH
  refine ⟨s ∪ t, fun n => F n + F' n, fun n => add_mem_zGraded (hF n) (hF' n), fun n hn => ?_, ?_⟩
  · change F n + F' n = 0
    rw [hs n fun h => hn (Finset.mem_union_left _ h),
      ht n fun h => hn (Finset.mem_union_right _ h), add_zero]
  · rw [Finset.sum_add_distrib,
      Finset.sum_subset (Finset.subset_union_left (s₂ := t)) fun n _ hn => hs n hn,
      Finset.sum_subset (Finset.subset_union_right (s₁ := s)) fun n _ hn => ht n hn]

/-- `Z^{(k+1)}` is closed under negation: negate the decomposition degreewise. -/
theorem neg_mem_zRing (hG : G ∈ zRing K k) : -G ∈ zRing K k := by
  obtain ⟨s, F, hF, hs, rfl⟩ := hG
  exact ⟨s, fun n => -F n, fun n => neg_mem_zGraded (hF n),
    fun n hn => show -F n = 0 by rw [hs n hn, neg_zero], (Finset.sum_neg_distrib ..).symm⟩

/-- **`Z^{(k+1)}` is closed under multiplication**: expanding the two finite sums gives a finite sum
of products whose `(d, e)` term lies in `Z^{(k+1)}_{d+e}` by
`HJO.Sym.zGraded_mul_zGraded_subset`, and collecting the terms with `d + e` equal exhibits the
product as a finite sum of members of the graded pieces. -/
theorem mul_mem_zRing (hG : G ∈ zRing K k) (hH : H ∈ zRing K k) : G * H ∈ zRing K k := by
  classical
  obtain ⟨s, F, hF, hs, rfl⟩ := hG
  obtain ⟨t, F', hF', ht, rfl⟩ := hH
  refine ⟨(s ×ˢ t).image fun p => p.1 + p.2,
    fun n => ∑ p ∈ (s ×ˢ t).filter fun p => p.1 + p.2 = n, F p.1 * F' p.2,
    fun n => sum_mem_zGraded fun p hp => ?_, fun n hn => Finset.sum_eq_zero fun p hp => ?_, ?_⟩
  · obtain ⟨-, hpn⟩ := Finset.mem_filter.1 hp
    exact hpn ▸ mul_mem_zGraded (hF p.1) (hF' p.2)
  · obtain ⟨hp1, hpn⟩ := Finset.mem_filter.1 hp
    exact absurd (hpn ▸ Finset.mem_image_of_mem (fun p => p.1 + p.2) hp1) hn
  · rw [Finset.sum_mul_sum, ← Finset.sum_product' s t fun a b => F a * F' b]
    exact (Finset.sum_fiberwise_of_maps_to
      (fun p hp => Finset.mem_image_of_mem (fun p => p.1 + p.2) hp) _).symm

/-- **The alphabet-graded part is a subring of `P°_{k+1}`**: the `Z^{(k)}` is a subring
of `P°_k`. Closure under differences is degreewise, `1` lies in the degree-zero piece, and the
product of two finite sums regroups by total degree. -/
@[hjo "lem_cm_zring_subring"]
def zSubring (K : Type*) [CommRing K] [IsDomain K] (k : ℕ) :
    Subring (AuxAlphabetSeriesFrac K (k + 1)) where
  carrier := zRing K k
  one_mem' := one_mem_zRing
  mul_mem' := mul_mem_zRing
  zero_mem' := zero_mem_zRing
  add_mem' := add_mem_zRing
  neg_mem' := neg_mem_zRing

/-- The subring `HJO.Sym.zSubring` is `HJO.Sym.zRing` and not some other set: this is the half of
`HJO.Sym.zSubring` that says *which* subring the lemma produces. -/
@[hjo "lem_cm_zring_subring", simp]
theorem coe_zSubring (K : Type*) [CommRing K] [IsDomain K] (k : ℕ) :
    (zSubring K k : Set (AuxAlphabetSeriesFrac K (k + 1))) = zRing K k :=
  rfl

/-- Membership in `HJO.Sym.zSubring`, unfolded. -/
@[simp]
theorem mem_zSubring : G ∈ zSubring K k ↔ G ∈ zRing K k := Iff.rfl

/-- A finite sum of members of `Z^{(k+1)}` is one. -/
theorem sum_mem_zRing {ι : Type*} {t : Finset ι} {F : ι → AuxAlphabetSeriesFrac K (k + 1)}
    (hF : ∀ i ∈ t, F i ∈ zRing K k) : ∑ i ∈ t, F i ∈ zRing K k :=
  sum_mem (S := zSubring K k) hF

/-! ### The merged coefficients are polynomial coefficients -/

/-- The polynomial in `y_{k+1}` over `𝕂(y₁, …, y_k)` that the coefficient of `G` at the
letter-monomial `x^α` is, when it is one: the preimage under `HJO.Sym.yFracEval`, which is unique by
`HJO.Sym.yFracEval_injective`. Off the range of that evaluation the value is `0`, and it is the
membership hypotheses below that exclude the case. -/
noncomputable def zPoly (K : Type*) [CommRing K] [IsDomain K] (k : ℕ)
    (G : AuxAlphabetSeriesFrac K (k + 1)) (α : ℕ →₀ ℕ) : Polynomial (AuxFrac K k) :=
  Function.invFun (yFracEval K k) (MvPowerSeries.coeff α G)

/-- The coefficients of `HJO.Sym.zPoly` are the merged coefficients of `HJO.Sym.zCoeff`: the `b`-th
one is the coefficient of `y_{k+1}^b x^α`. This holds by definition, with no hypothesis. -/
theorem coeff_zPoly (G : AuxAlphabetSeriesFrac K (k + 1)) (α : ℕ →₀ ℕ) (b : ℕ) :
    (zPoly K k G α).coeff b = zCoeff K k G (α.optionElim b) := by
  rw [zCoeff, Finsupp.some_optionElim, Finsupp.optionElim_apply_none, yFracCoeff, zPoly]

/-- `HJO.Sym.zPoly` recovers the coefficient it came from, on the series whose coefficients are
polynomial in `y_{k+1}`. -/
theorem yFracEval_zPoly {α : ℕ →₀ ℕ}
    (hG : MvPowerSeries.coeff α G ∈ (yFracEval K k).range) :
    yFracEval K k (zPoly K k G α) = MvPowerSeries.coeff α G :=
  Function.invFun_eq (RingHom.mem_range.1 hG)

/-- **A member of `Z^{(k+1)}` is determined by its merged coefficients**: under
`MvPowerSeries.ext` the claim is `Polynomial.ext` on the polynomials of `HJO.Sym.zPoly`. This is
what makes every identity below provable one merged coefficient at a time. -/
theorem eq_of_zCoeff_eq (hG : ∀ α : ℕ →₀ ℕ, MvPowerSeries.coeff α G ∈ (yFracEval K k).range)
    (hH : ∀ α : ℕ →₀ ℕ, MvPowerSeries.coeff α H ∈ (yFracEval K k).range)
    (h : ∀ ν, zCoeff K k G ν = zCoeff K k H ν) : G = H := by
  refine MvPowerSeries.ext fun α => ?_
  rw [← Function.invFun_eq (f := yFracEval K k) (RingHom.mem_range.1 (hG α)),
    ← Function.invFun_eq (f := yFracEval K k) (RingHom.mem_range.1 (hH α))]
  refine congrArg _ (Polynomial.ext fun b => ?_)
  rw [show Function.invFun (yFracEval K k) (MvPowerSeries.coeff α G) = zPoly K k G α from rfl,
    show Function.invFun (yFracEval K k) (MvPowerSeries.coeff α H) = zPoly K k H α from rfl,
    coeff_zPoly, coeff_zPoly, h]

/-! ### The relabellings preserve each graded piece -/

/-- **`ŝ_ρ` preserves each graded piece**, elementwise: the coefficient of `ŝ_ρ G` at a
letter-monomial `x^α` with `|α| ≤ d` is a scalar multiple of the single power `y_{k+1}^{d-|α|}` by
`HJO.Sym.coeff_zPerm_of_mem_zGraded`, and it vanishes for `|α| > d` by
`HJO.Sym.coeff_zPerm_eq_zero_of_mem_zGraded`. -/
theorem zPerm_mem_zGraded (ρ : Equiv.Perm (Option ℕ)) (hG : G ∈ zGraded K k d) :
    zPerm K k ρ G ∈ zGraded K k d := by
  refine ⟨fun α b hb => ⟨zCoeff K k G (Finsupp.equivMapDomain ρ.symm (α.optionElim b)), ?_⟩,
    fun α hα => coeff_zPerm_eq_zero_of_mem_zGraded ρ hG hα⟩
  have hb' : d - Finsupp.degree α = b := by omega
  rw [coeff_zPerm_of_mem_zGraded ρ hG (by omega), hb']

/-- **`ŝ_ρ` preserves each graded piece**: `ŝ_ρ(Z^{(k+1)}_d) ⊆ Z^{(k+1)}_d`. A relabelling carries a
merged monomial to one with the same letters counted with multiplicity, hence of the same total
degree, and it acts coefficientwise. -/
@[hjo "lem_cm_zperm_graded"]
theorem zPerm_image_zGraded_subset (K : Type*) [CommRing K] [IsDomain K] (k d : ℕ)
    (ρ : Equiv.Perm (Option ℕ)) : zPerm K k ρ '' zGraded K k d ⊆ zGraded K k d := by
  rintro _ ⟨G, hG, rfl⟩
  exact zPerm_mem_zGraded ρ hG

/-- `ŝ_ρ` kills `0`: every merged coefficient of `0` is `0`. -/
@[simp]
theorem zPerm_zero (ρ : Equiv.Perm (Option ℕ)) :
    zPerm K k ρ (0 : AuxAlphabetSeriesFrac K (k + 1)) = 0 := by
  refine MvPowerSeries.ext fun α => ?_
  rw [coeff_zPerm, MvPowerSeries.coeff_zero,
    finsum_congr (f := fun b : ℕ => auxFracCastSucc K k
        (zCoeff K k (0 : AuxAlphabetSeriesFrac K (k + 1))
          (Finsupp.equivMapDomain ρ.symm (α.optionElim b)))
      * yFrac K (Fin.last k) ^ b) (g := fun _ : ℕ => 0)
      fun b => by rw [zCoeff, MvPowerSeries.coeff_zero, yFracCoeff_zero, map_zero, zero_mul],
    finsum_zero]

/-- `ŝ_ρ` is additive over a finite sum of members of `Z^{(k+1)}`. -/
theorem zPerm_sum_of_mem_zRing (ρ : Equiv.Perm (Option ℕ)) {ι : Type*} {t : Finset ι}
    {F : ι → AuxAlphabetSeriesFrac K (k + 1)} (hF : ∀ i ∈ t, F i ∈ zRing K k) :
    zPerm K k ρ (∑ i ∈ t, F i) = ∑ i ∈ t, zPerm K k ρ (F i) := by
  classical
  induction t using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons,
      zPerm_add_of_mem_zRing ρ (hF a (Finset.mem_cons_self ..))
        (sum_mem_zRing fun i hi => hF i (Finset.mem_cons_of_mem hi)),
      ih fun i hi => hF i (Finset.mem_cons_of_mem hi)]

/-- **`ŝ_ρ` maps `Z^{(k+1)}` into itself**: it acts on the decomposition degreewise, and each piece
stays in its own degree by `HJO.Sym.zPerm_mem_zGraded`. -/
theorem zPerm_mem_zRing (ρ : Equiv.Perm (Option ℕ)) (hG : G ∈ zRing K k) :
    zPerm K k ρ G ∈ zRing K k := by
  obtain ⟨s, F, hF, hs, rfl⟩ := hG
  refine ⟨s, fun n => zPerm K k ρ (F n), fun n => zPerm_mem_zGraded ρ (hF n), fun n hn => ?_,
    zPerm_sum_of_mem_zRing ρ fun n _ => zGraded_subset_zRing K k n (hF n)⟩
  change zPerm K k ρ (F n) = 0
  rw [hs n hn, zPerm_zero]

/-! ### The merged coefficients of a relabelled series -/

/-- **The merged coefficients of `ŝ_ρ G` are those of `G` read at the relabelled exponent vectors.**
This is the computational content of the relabelling: the sum defining a coefficient of `ŝ_ρ G` has
finite support once `G` lies in `Z^{(k+1)}`, so it is the evaluation at `y_{k+1}` of an honest
polynomial whose coefficients are the merged coefficients of `G` at the relabelled vectors, and
extracting the `ν none`-th coefficient of that polynomial gives the claim. -/
theorem zCoeff_zPerm (ρ : Equiv.Perm (Option ℕ)) (hG : G ∈ zRing K k) (ν : Option ℕ →₀ ℕ) :
    zCoeff K k (zPerm K k ρ G) ν = zCoeff K k G (Finsupp.equivMapDomain ρ.symm ν) := by
  classical
  obtain ⟨N, hN⟩ := exists_zCoeff_eq_zero_of_mem_zRing hG
  have hczero : ∀ (α : ℕ →₀ ℕ) (b : ℕ), N < b + Finsupp.degree α →
      zCoeff K k G (Finsupp.equivMapDomain ρ.symm (α.optionElim b)) = 0 := fun α b hb =>
    hN _ (by rw [degree_equivMapDomain, degree_optionElim]; omega)
  have key : ∀ (α : ℕ →₀ ℕ) (b₀ : ℕ), yFracCoeff K k (MvPowerSeries.coeff α (zPerm K k ρ G)) b₀
      = zCoeff K k G (Finsupp.equivMapDomain ρ.symm (α.optionElim b₀)) := by
    intro α b₀
    have hkey : MvPowerSeries.coeff α (zPerm K k ρ G)
        = yFracEval K k (∑ b ∈ Finset.range (N + 1),
            Polynomial.C (zCoeff K k G (Finsupp.equivMapDomain ρ.symm (α.optionElim b)))
              * Polynomial.X ^ b) := by
      rw [coeff_zPerm, map_sum]
      refine (finsum_eq_sum_of_support_subset _ (s := Finset.range (N + 1)) fun b hb => ?_).trans
        (Finset.sum_congr rfl fun b _ => (yFracEval_C_mul_X_pow _ b).symm)
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hbN
      refine hb ?_
      change auxFracCastSucc K k
          (zCoeff K k G (Finsupp.equivMapDomain ρ.symm (α.optionElim b)))
            * yFrac K (Fin.last k) ^ b = 0
      rw [hczero α b (by omega), map_zero, zero_mul]
    rw [hkey, yFracCoeff_yFracEval, Polynomial.finsetSum_coeff,
      Finset.sum_congr rfl fun b _ => Polynomial.coeff_C_mul_X_pow _ b b₀,
      Finset.sum_ite_eq (Finset.range (N + 1)) b₀
        fun b => zCoeff K k G (Finsupp.equivMapDomain ρ.symm (α.optionElim b))]
    by_cases hb₀ : b₀ ∈ Finset.range (N + 1)
    · rw [ite_eq_left hb₀]
    · rw [ite_eq_right hb₀, hczero α b₀ (by simp only [Finset.mem_range] at hb₀; omega)]
  rw [zCoeff, key ν.some (ν none), Finsupp.optionElim_some]

/-- **The relabellings compose**: `ŝ_ρ(ŝ_{ρ'}(G)) = ŝ_{ρρ'}(G)` for `G` in `Z^{(k+1)}`, that is,
`ŝ_ρ ∘ ŝ_{ρ'} = ŝ_{ρρ'}` as maps of `Z^{(k+1)}`. Both sides read a merged coefficient of
`G` at a relabelled exponent vector, and `(ρρ')^{-1}` reindexes by `ρ'^{-1}` after `ρ^{-1}`. -/
@[hjo "lem_cm_zperm_comp"]
theorem zPerm_zPerm (ρ ρ' : Equiv.Perm (Option ℕ)) (hG : G ∈ zRing K k) :
    zPerm K k ρ (zPerm K k ρ' G) = zPerm K k (ρ * ρ') G := by
  refine MvPowerSeries.ext fun α => ?_
  rw [coeff_zPerm, coeff_zPerm]
  refine finsum_congr fun b => ?_
  rw [zCoeff_zPerm ρ' hG, show (ρ * ρ').symm = ρ.symm.trans ρ'.symm from rfl,
    Finsupp.equivMapDomain_trans]

/-- `ŝ_ρ` at the identity permutation is the identity on `Z^{(k+1)}`: a coefficient of `G` there is
already a polynomial in `y_{k+1}`, and the sum reassembles it. -/
@[simp]
theorem zPerm_one (hG : G ∈ zRing K k) : zPerm K k (1 : Equiv.Perm (Option ℕ)) G = G := by
  have h1 : ∀ μ : Option ℕ →₀ ℕ,
      Finsupp.equivMapDomain (1 : Equiv.Perm (Option ℕ)).symm μ = μ :=
    fun μ => Finsupp.ext fun _ => rfl
  refine MvPowerSeries.ext fun α => ?_
  rw [coeff_zPerm, ← yFracEval_zPoly (coeff_mem_range_yFracEval_of_mem_zRing hG α),
    yFracEval_apply,
    finsum_congr (g := fun b : ℕ => auxFracCastSucc K k ((zPoly K k G α).coeff b)
        * yFrac K (Fin.last k) ^ b)
      fun b => by rw [h1, ← coeff_zPoly]]
  refine finsum_eq_sum_of_support_subset _ fun b hb => ?_
  simp only [Finset.mem_coe, Polynomial.mem_support_iff]
  intro h
  refine hb ?_
  change auxFracCastSucc K k ((zPoly K k G α).coeff b) * yFrac K (Fin.last k) ^ b = 0
  rw [h, map_zero, zero_mul]

/-- **`ŝ_{ρ^{-1}}` undoes `ŝ_ρ`** on `Z^{(k+1)}`: the composition is `ŝ_{ρ^{-1}ρ} = ŝ_{id}`, which
is the identity. -/
theorem zPerm_zPerm_symm (ρ : Equiv.Perm (Option ℕ)) (hG : G ∈ zRing K k) :
    zPerm K k ρ⁻¹ (zPerm K k ρ G) = G := by
  rw [zPerm_zPerm ρ⁻¹ ρ hG, inv_mul_cancel, zPerm_one hG]

/-! ### The merged coefficients of a product -/

/-- The factorisations of a merged exponent vector, in two halves: `ν₁ + ν₂ = ν` says exactly that
the letter parts add to `ν.some` and the `y`-exponents to `ν none`. -/
theorem antidiagonal_optionElim_bij {ν : Option ℕ →₀ ℕ} {ν₁ ν₂ : Option ℕ →₀ ℕ} :
    ν₁ + ν₂ = ν ↔ ν₁.some + ν₂.some = ν.some ∧ ν₁ none + ν₂ none = ν none := by
  refine ⟨fun h => ⟨?_, by rw [← h, Finsupp.add_apply]⟩, fun ⟨h1, h2⟩ => Finsupp.ext fun a => ?_⟩
  · refine Finsupp.ext fun i => ?_
    simp only [Finsupp.add_apply, Finsupp.some_apply]
    rw [← h, Finsupp.add_apply]
  · cases a with
    | none => rw [Finsupp.add_apply, h2]
    | some i =>
      have h := congrArg (fun f : ℕ →₀ ℕ => f i) h1
      simp only [Finsupp.add_apply, Finsupp.some_apply] at h
      rw [Finsupp.add_apply, h]

/-- **The merged coefficients of a product are the convolution of the merged coefficients**: the
coefficient of `z^ν` in `GH` is the sum, over the factorisations `ν = ν₁ + ν₂`, of the product of
the coefficients of `z^{ν₁}` in `G` and of `z^{ν₂}` in `H`. Under `HJO.Sym.zPoly` this is
`Polynomial.coeff_mul` inside `MvPowerSeries.coeff_mul`, the two antidiagonals — of the letter part
and of the `y`-exponent — assembling into the antidiagonal of the merged vector. -/
theorem zCoeff_mul (hG : G ∈ zRing K k) (hH : H ∈ zRing K k) (ν : Option ℕ →₀ ℕ) :
    zCoeff K k (G * H) ν
      = ∑ p ∈ Finset.antidiagonal ν, zCoeff K k G p.1 * zCoeff K k H p.2 := by
  classical
  have hGH : ∀ α : ℕ →₀ ℕ, MvPowerSeries.coeff α (G * H)
      = yFracEval K k (∑ p ∈ Finset.antidiagonal α, zPoly K k G p.1 * zPoly K k H p.2) := by
    intro α
    rw [map_sum, MvPowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_mul, yFracEval_zPoly (coeff_mem_range_yFracEval_of_mem_zRing hG p.1),
      yFracEval_zPoly (coeff_mem_range_yFracEval_of_mem_zRing hH p.2)]
  rw [zCoeff, hGH, yFracCoeff_yFracEval, Polynomial.finsetSum_coeff]
  rw [Finset.sum_congr rfl fun p _ => Polynomial.coeff_mul (zPoly K k G p.1) (zPoly K k H p.2)
    (ν none)]
  rw [← Finset.sum_product' (Finset.antidiagonal ν.some) (Finset.antidiagonal (ν none))
    fun p b => (zPoly K k G p.1).coeff b.1 * (zPoly K k H p.2).coeff b.2]
  refine Finset.sum_nbij'
    (i := fun x : ((ℕ →₀ ℕ) × (ℕ →₀ ℕ)) × (ℕ × ℕ) =>
      (x.1.1.optionElim x.2.1, x.1.2.optionElim x.2.2))
    (j := fun p : (Option ℕ →₀ ℕ) × (Option ℕ →₀ ℕ) =>
      ((p.1.some, p.2.some), (p.1 none, p.2 none))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨α₁, α₂⟩, ⟨b₁, b₂⟩⟩ hx
    simp only [Finset.mem_product, Finset.mem_antidiagonal] at hx
    refine Finset.mem_antidiagonal.2 (antidiagonal_optionElim_bij.2 ⟨?_, ?_⟩)
    · rw [Finsupp.some_optionElim, Finsupp.some_optionElim]; exact hx.1
    · rw [Finsupp.optionElim_apply_none, Finsupp.optionElim_apply_none]; exact hx.2
  · rintro ⟨ν₁, ν₂⟩ hp
    obtain ⟨h1, h2⟩ := antidiagonal_optionElim_bij.1 (Finset.mem_antidiagonal.1 hp)
    exact Finset.mem_product.2 ⟨Finset.mem_antidiagonal.2 h1, Finset.mem_antidiagonal.2 h2⟩
  · rintro ⟨⟨α₁, α₂⟩, ⟨b₁, b₂⟩⟩ -
    simp only [Finsupp.some_optionElim, Finsupp.optionElim_apply_none]
  · rintro ⟨ν₁, ν₂⟩ -
    simp only [Finsupp.optionElim_some]
  · rintro ⟨⟨α₁, α₂⟩, ⟨b₁, b₂⟩⟩ -
    rw [coeff_zPoly, coeff_zPoly]

/-! ### The relabellings are ring automorphisms -/

/-- Relabelling the merged alphabet is additive on exponent vectors: the relabelled monomial of a
product is the product of the relabelled monomials. -/
theorem equivMapDomain_add {σ : Type*} (e : σ ≃ σ) (ν₁ ν₂ : σ →₀ ℕ) :
    Finsupp.equivMapDomain e (ν₁ + ν₂)
      = Finsupp.equivMapDomain e ν₁ + Finsupp.equivMapDomain e ν₂ := by
  rw [Finsupp.equivMapDomain_eq_mapDomain, Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.equivMapDomain_eq_mapDomain, Finsupp.mapDomain_add]

/-- Relabelling along a permutation undoes relabelling along its inverse. -/
theorem equivMapDomain_equivMapDomain_symm {σ : Type*} (e : Equiv.Perm σ) (ν : σ →₀ ℕ) :
    Finsupp.equivMapDomain e (Finsupp.equivMapDomain e.symm ν) = ν := by
  rw [← Finsupp.equivMapDomain_trans, Equiv.symm_trans_self, Finsupp.equivMapDomain_refl]

/-- Relabelling along the inverse of a permutation undoes relabelling along it. -/
theorem equivMapDomain_symm_equivMapDomain {σ : Type*} (e : Equiv.Perm σ) (ν : σ →₀ ℕ) :
    Finsupp.equivMapDomain e.symm (Finsupp.equivMapDomain e ν) = ν := by
  rw [← Finsupp.equivMapDomain_trans, Equiv.self_trans_symm, Finsupp.equivMapDomain_refl]

/-- **`ŝ_ρ` is multiplicative on `Z^{(k+1)}`**: relabelling a merged monomial commutes with
multiplying two of them, which on merged coefficients is the statement that reindexing the
factorisations of `ρ^{-1}ν` along `ρ` is a bijection onto the factorisations of `ν`. -/
theorem zPerm_mul_of_mem_zRing (ρ : Equiv.Perm (Option ℕ)) (hG : G ∈ zRing K k)
    (hH : H ∈ zRing K k) : zPerm K k ρ (G * H) = zPerm K k ρ G * zPerm K k ρ H := by
  classical
  refine eq_of_zCoeff_eq
    (coeff_mem_range_yFracEval_of_mem_zRing (zPerm_mem_zRing ρ (mul_mem_zRing hG hH)))
    (coeff_mem_range_yFracEval_of_mem_zRing
      (mul_mem_zRing (zPerm_mem_zRing ρ hG) (zPerm_mem_zRing ρ hH))) fun ν => ?_
  rw [zCoeff_zPerm ρ (mul_mem_zRing hG hH), zCoeff_mul hG hH,
    zCoeff_mul (zPerm_mem_zRing ρ hG) (zPerm_mem_zRing ρ hH)]
  refine (Finset.sum_nbij'
    (i := fun p => (Finsupp.equivMapDomain ρ.symm p.1, Finsupp.equivMapDomain ρ.symm p.2))
    (j := fun p => (Finsupp.equivMapDomain ρ p.1, Finsupp.equivMapDomain ρ p.2)) ?_ ?_ ?_ ?_
    ?_).symm
  · rintro ⟨ν₁, ν₂⟩ hp
    exact Finset.mem_antidiagonal.2
      (by rw [← equivMapDomain_add, Finset.mem_antidiagonal.1 hp])
  · rintro ⟨ν₁, ν₂⟩ hp
    exact Finset.mem_antidiagonal.2 (by
      rw [← equivMapDomain_add, Finset.mem_antidiagonal.1 hp,
        equivMapDomain_equivMapDomain_symm])
  · rintro ⟨ν₁, ν₂⟩ -
    simp only [Prod.mk.injEq]
    exact ⟨equivMapDomain_equivMapDomain_symm ρ ν₁, equivMapDomain_equivMapDomain_symm ρ ν₂⟩
  · rintro ⟨ν₁, ν₂⟩ -
    simp only [Prod.mk.injEq]
    exact ⟨equivMapDomain_symm_equivMapDomain ρ ν₁, equivMapDomain_symm_equivMapDomain ρ ν₂⟩
  · rintro ⟨ν₁, ν₂⟩ -
    rw [zCoeff_zPerm ρ hG, zCoeff_zPerm ρ hH]

/-- **`ŝ_ρ` fixes the lower coefficient field**: the constant series of a scalar of
`𝕂(y₁, …, y_k)` is the merged monomial at the empty exponent vector, which every relabelling fixes.
With `HJO.Sym.zPerm_mul_of_mem_zRing` this is the "`𝕂(y₁, …, y_{k-1})`-algebra
automorphism", stated without an `Algebra` instance between the two fraction fields. -/
theorem zPerm_C (ρ : Equiv.Perm (Option ℕ)) (c : AuxFrac K k) :
    zPerm K k ρ (MvPowerSeries.C (auxFracCastSucc K k c)) = MvPowerSeries.C (auxFracCastSucc K k c)
    := by
  have h : (MvPowerSeries.C (auxFracCastSucc K k c) : AuxAlphabetSeriesFrac K (k + 1))
      = zMonomial K k 0 c := by
    rw [zMonomial, Finsupp.some_zero, Finsupp.coe_zero, Pi.zero_apply, pow_zero, mul_one,
      MvPowerSeries.monomial_zero_eq_C_apply]
  rw [h, zPerm_zMonomial, Finsupp.equivMapDomain_zero]

/-- The constant series of a scalar of the lower coefficient field lies in `Z^{(k+1)}`. -/
theorem C_auxFracCastSucc_mem_zRing (c : AuxFrac K k) :
    (MvPowerSeries.C (auxFracCastSucc K k c) : AuxAlphabetSeriesFrac K (k + 1)) ∈ zRing K k := by
  refine zGraded_subset_zRing K k 0 ?_
  have h : (MvPowerSeries.C (auxFracCastSucc K k c) : AuxAlphabetSeriesFrac K (k + 1))
      = MvPowerSeries.monomial (0 : ℕ →₀ ℕ)
        (auxFracCastSucc K k c * yFrac K (Fin.last k) ^ 0) := by
    rw [pow_zero, mul_one, MvPowerSeries.monomial_zero_eq_C_apply]
  rw [h]
  exact monomial_mem_zGraded (by simp) c

/-- `ŝ_ρ` as a self-map of the subring `Z^{(k+1)}`, which it is by `HJO.Sym.zPerm_mem_zRing`. -/
noncomputable def zPermSubring (K : Type*) [CommRing K] [IsDomain K] (k : ℕ)
    (ρ : Equiv.Perm (Option ℕ)) (G : zSubring K k) : zSubring K k :=
  ⟨zPerm K k ρ (G : AuxAlphabetSeriesFrac K (k + 1)),
    mem_zSubring.2 (zPerm_mem_zRing ρ (mem_zSubring.1 G.2))⟩

/-- The self-map of `HJO.Sym.zPermSubring` is `ŝ_ρ`. -/
@[simp]
theorem coe_zPermSubring (ρ : Equiv.Perm (Option ℕ)) (G : zSubring K k) :
    (zPermSubring K k ρ G : AuxAlphabetSeriesFrac K (k + 1))
      = zPerm K k ρ (G : AuxAlphabetSeriesFrac K (k + 1)) :=
  rfl

/-- **`ŝ_ρ` is a ring automorphism of `Z^{(k+1)}` with inverse `ŝ_{ρ^{-1}}`**: this is
`HJO.Sym.zPermEquiv`, the algebra half of which is `HJO.Sym.zPerm_C`. Restricted to the subring
there is nothing left to hypothesise, so the statement is an honest `RingAut`. -/
@[hjo "lem_cm_zperm_auto"]
noncomputable def zPermEquiv (K : Type*) [CommRing K] [IsDomain K] (k : ℕ)
    (ρ : Equiv.Perm (Option ℕ)) : RingAut (zSubring K k) where
  toFun := zPermSubring K k ρ
  invFun := zPermSubring K k ρ⁻¹
  left_inv G := Subtype.ext (by
    rw [coe_zPermSubring, coe_zPermSubring, zPerm_zPerm_symm ρ (mem_zSubring.1 G.2)])
  right_inv G := Subtype.ext (by
    rw [coe_zPermSubring, coe_zPermSubring, zPerm_zPerm ρ ρ⁻¹ (mem_zSubring.1 G.2),
      mul_inv_cancel, zPerm_one (mem_zSubring.1 G.2)])
  map_mul' G H := Subtype.ext (by
    simp only [coe_zPermSubring, Subring.coe_mul]
    exact zPerm_mul_of_mem_zRing ρ (mem_zSubring.1 G.2) (mem_zSubring.1 H.2))
  map_add' G H := Subtype.ext (by
    simp only [coe_zPermSubring, Subring.coe_add]
    exact zPerm_add_of_mem_zRing ρ (mem_zSubring.1 G.2) (mem_zSubring.1 H.2))

/-- The automorphism of `HJO.Sym.zPermEquiv` is `ŝ_ρ`. -/
@[hjo "lem_cm_zperm_auto", simp]
theorem zPermEquiv_apply (ρ : Equiv.Perm (Option ℕ)) (G : zSubring K k) :
    (zPermEquiv K k ρ G : AuxAlphabetSeriesFrac K (k + 1)) = zPerm K k ρ G :=
  rfl

/-- The inverse of `HJO.Sym.zPermEquiv` at `ρ` is the one at `ρ^{-1}`, which is the clause
"with inverse `ŝ_{ρ^{-1}}`". -/
@[hjo "lem_cm_zperm_auto", simp]
theorem zPermEquiv_symm_apply (ρ : Equiv.Perm (Option ℕ)) (G : zSubring K k) :
    ((zPermEquiv K k ρ).symm G : AuxAlphabetSeriesFrac K (k + 1)) = zPerm K k ρ⁻¹ G :=
  rfl

/-! ### Interchanging two adjacent letters -/

/-- The letter of the merged alphabet at offset `r` from the level: the letter
`z^{(k+1)}_{k+1+r}`, which is the distinguished letter `y_{k+1}` at `r = 0` and the letter `x_r` at
`r ≥ 1`. Written by recursion, so that no `ℕ`-subtraction enters. -/
def zLetter : ℕ → Option ℕ
  | 0 => none
  | (r + 1) => some r

/-- The letter at offset `0` is the distinguished letter `y_{k+1}`. -/
@[simp] theorem zLetter_zero : zLetter 0 = none := rfl

/-- The letter at offset `r + 1` is the letter `x_{r+1}`. -/
@[simp] theorem zLetter_succ (r : ℕ) : zLetter (r + 1) = some r := rfl

/-- Distinct offsets name distinct letters. -/
theorem zLetter_injective : Function.Injective zLetter := by
  intro r r' h
  cases r with
  | zero => cases r' with
    | zero => rfl
    | succ r' => exact absurd h (by simp)
  | succ r => cases r' with
    | zero => exact absurd h (by simp)
    | succ r' => exact congrArg _ (Option.some_injective ℕ h)

/-- The transposition of the merged alphabet interchanging the letters at offsets `r` and `r + 1`
from the level: the transposition of `m` and `m + 1` at `m = k + 1 + r`. -/
def zSwapEquiv (r : ℕ) : Equiv.Perm (Option ℕ) :=
  Equiv.swap (zLetter r) (zLetter (r + 1))

/-- The interchange at offset `0` swaps the distinguished letter `y_{k+1}` with the first letter
`x_1`: this is the `ŝ_k`, the one with no extension to `P°_{k+1}`. -/
@[simp]
theorem zSwapEquiv_zero : zSwapEquiv 0 = Equiv.swap none (some 0) := rfl

/-- The interchange at a positive offset swaps two letters: this is the `ŝ_m` for
`m > k`, the restriction to `Z^{(k+1)}` of the automorphism of `P°_{k+1}` interchanging `x_{r+1}`
and `x_{r+2}`. -/
@[simp]
theorem zSwapEquiv_succ (r : ℕ) : zSwapEquiv (r + 1) = Equiv.swap (some r) (some (r + 1)) := rfl

/-- An interchange is an involution. -/
@[simp]
theorem zSwapEquiv_mul_self (r : ℕ) : zSwapEquiv r * zSwapEquiv r = 1 :=
  Equiv.swap_mul_self _ _

/-- An interchange is its own inverse. -/
@[simp]
theorem zSwapEquiv_inv (r : ℕ) : (zSwapEquiv r)⁻¹ = zSwapEquiv r :=
  inv_eq_of_mul_eq_one_left (zSwapEquiv_mul_self r)

/-- **Interchanging two merged variables**: `ŝ_m := ŝ_t` for the transposition `t` of the merged
alphabet interchanging the letters of indices `m` and `m + 1`, at `m = k + 1 + r`. The
range `m ≥ k + 1` — the general `m ≥ k` at the level `k + 1` — is the whole of `r : ℕ`, which is
why the offset and not `m` is carried. At `r = 0` the map interchanges `y_{k+1}` with `x_1` and is
not induced by any substitution in `P°_{k+1}`; at `r ≥ 1` it is the restriction of the substitution
interchanging two letters. -/
@[hjo "def_cm_zswap"]
noncomputable def zSwap (K : Type*) [CommRing K] [IsDomain K] (k r : ℕ) :
    AuxAlphabetSeriesFrac K (k + 1) → AuxAlphabetSeriesFrac K (k + 1) :=
  zPerm K k (zSwapEquiv r)

/-- `ŝ_m` is the relabelling along the transposition, by definition. -/
theorem zSwap_apply (r : ℕ) (G : AuxAlphabetSeriesFrac K (k + 1)) :
    zSwap K k r G = zPerm K k (zSwapEquiv r) G :=
  rfl

/-- **`ŝ_m` interchanges the two letters and fixes the rest**, read on a merged monomial: it carries
`c z^ν` to `c z^{tν}` for the transposition `t`. Together with `HJO.Sym.zSwap` this is the whole of
`HJO.Sym.zSwap`. -/
@[hjo "def_cm_zswap"]
theorem zSwap_zMonomial (r : ℕ) (ν : Option ℕ →₀ ℕ) (c : AuxFrac K k) :
    zSwap K k r (zMonomial K k ν c)
      = zMonomial K k (Finsupp.equivMapDomain (zSwapEquiv r) ν) c :=
  zPerm_zMonomial _ _ _

/-- `ŝ_m` maps `Z^{(k+1)}_d` into itself. -/
theorem zSwap_mem_zGraded (r : ℕ) (hG : G ∈ zGraded K k d) : zSwap K k r G ∈ zGraded K k d :=
  zPerm_mem_zGraded _ hG

/-- `ŝ_m` maps `Z^{(k+1)}` into itself. -/
theorem zSwap_mem_zRing (r : ℕ) (hG : G ∈ zRing K k) : zSwap K k r G ∈ zRing K k :=
  zPerm_mem_zRing _ hG

/-- `ŝ_m` is an involution on `Z^{(k+1)}`: the transposition is, and the relabellings compose. -/
@[simp]
theorem zSwap_zSwap (r : ℕ) (hG : G ∈ zRing K k) : zSwap K k r (zSwap K k r G) = G := by
  rw [zSwap_apply, zSwap_apply, zPerm_zPerm _ _ hG, zSwapEquiv_mul_self, zPerm_one hG]

end HJO.Sym
