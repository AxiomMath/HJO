/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Classical.CompGessel
public import HJO.Classical.HomogeneousPreimage
public import HJO.Classical.HsymmSpan
public import HJO.Classical.OmegaExchange
public import HJO.SignExtraction.GesselIndependent
public import HJO.Shuffle.GesselReversal
public meta import HJO.Attr

/-! # The involution complements the descent sets

Five results, the whole of Gessel's identity as this library proves it: the involution
`ω` of `Λ` acts on a fundamental quasisymmetric expansion of a realised symmetric function by
complementing each descent set, and `ω₋` does the same up to the sign `(-1)^n`.

The chain is: one degree at a time, from the spanning of a graded piece by the products `h_α`; then
all degrees at once, by splitting into homogeneous components; then at an arbitrary finite index
set, by grouping; then with the reversal discarded; then with the sign.

## Main statements

* `HJO.ParkingFunctions.realisation_omegaStd_of_component`.
* `HJO.ParkingFunctions.realisation_omegaStd_canonical`.
* `HJO.ParkingFunctions.realisation_omegaStd_conjugate`.
* `HJO.ParkingFunctions.realisation_omegaStd_complement`.
* `HJO.ParkingFunctions.realisation_plethNegate_gessel`.

## Implementation notes

*The "`c_T ∈ 𝕜` for each `T ⊆ \{1,…,d-1\}`" is a function `Finset ℕ → K` summed over
`(Finset.Ico 1 d).powerset`.* Nothing outside the window is read, and the powerset is that
index set verbatim.

*The first result is proved by exhibiting a submodule.* `HJO.ParkingFunctions.omegaCompat` is the
set of `f` admitting *some* coefficient family witnessing both the expansion of `ι f` and the
complemented expansion of `ι(ω f)`; it is a submodule because two witnesses add, and it contains
every `h_α` because `HJO.ParkingFunctions.realisation_completeHomogComp` and
`HJO.ParkingFunctions.realisation_elemSymmComp` expand `h_α` and `e_α = ω(h_α)` over the *same*
permutations. So `HJO.Sym.lambdaComp_le_completeHomogCompSpan` puts every element of `Λ_d` in it,
and `HJO.ParkingFunctions.linearIndepOn_gessel` then identifies the witness with the family the
statement is given — that is the one place independence is spent.

*No separate treatment of `d = 0` is needed.* `HJO.Sym.lambdaComp_le_completeHomogCompSpan` holds
at `0` as well,
the empty composition giving `1 = h_{()}`, so the same argument covers every degree.

*`HJO.ParkingFunctions.realisation_omegaStd_conjugate` does not need
`HJO.ParkingFunctions.descentReverse_sdiff_injective`.* The textbook argument groups the hypothesis
by the value of `S_i` and the conclusion by the value of `S_i^†`, and needs `T ↦ T^†` injective to
match them. Grouping *both* by the value of `S_i` needs no such thing: the regrouping lemma is used
in the same direction twice, once on each side.

*A field is needed from `HJO.ParkingFunctions.realisation_omegaStd_canonical` on.*
`HJO.gessel_reverse_sum` is stated over a field, and the reversal enters every statement from the
canonical one onwards. The base field `𝕜 = ℚ(q,u)` supplies it.

*The hypothesis `n ≥ 1` is nowhere needed.* At `n = 0` the window is empty, the only index set is
`∅`, and every statement reduces to an identity between constants.

## References

The results `HJO.ParkingFunctions.realisation_omegaStd_of_component`,
`HJO.ParkingFunctions.realisation_omegaStd_canonical`,
`HJO.ParkingFunctions.realisation_omegaStd_conjugate`,
`HJO.ParkingFunctions.realisation_omegaStd_complement` and
`HJO.ParkingFunctions.realisation_plethNegate_gessel`, on the involution on characteristic
functions.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Sym

/-- The total degree of an exponent vector as a sum over its support, which is the form the
degree of a monomial of a fundamental is computed in. -/
theorem degHom_eq_sum (d : ℕ →₀ ℕ) : degHom d = ∑ i ∈ d.support, d i := rfl

end HJO.Sym

namespace HJO.ParkingFunctions

open HJO.Sym

/-! ### Two facts about fundamentals -/

/-- **A fundamental of degree `n` lives in total degree `n`**: a monomial of any other degree does
not occur in `F_{n,S}`, whatever `S` is. -/
theorem coeff_gessel_eq_zero_of_degHom_ne (K : Type*) [CommRing K] {n : ℕ} {S : Finset ℕ}
    {d : ℕ →₀ ℕ} (h : degHom d ≠ n) : MvPowerSeries.coeff d (gessel K n S) = 0 := by
  refine coeff_gessel_eq_zero K ?_
  rintro ⟨i, -, -, rfl⟩
  refine h ?_
  set w : Fin n → ℕ := fun k => i ((k : ℕ) + 1) with hw
  have hd : ∑ j ∈ Icc 1 n, Finsupp.single (i j) 1 = wordExponent w :=
    sum_Icc_single_eq_wordExponent n i
  have hall : ∀ k, w k ∈ (wordExponent w).support := fun k =>
    (mem_support_wordExponent w (w k)).2 ⟨k, rfl⟩
  rw [hd, degHom_eq_sum]
  exact sum_wordExponent w hall

/-- **The coefficients of a canonical fundamental expansion are determined.** This is
`HJO.ParkingFunctions.linearIndepOn_gessel` in the form the lemmas below use it: two families of
scalars indexed by the subsets of the window that give the same combination of the `F_{n,S}`
agree. -/
theorem eq_of_sum_gessel_eq (K : Type*) [CommRing K] {n : ℕ} {a b : Finset ℕ → K}
    (h : ∑ S ∈ (Ico 1 n).powerset, a S • gessel K n S
       = ∑ S ∈ (Ico 1 n).powerset, b S • gessel K n S) :
    ∀ S ∈ (Ico 1 n).powerset, a S = b S := by
  classical
  have hli := linearIndepOn_gessel K n
  rw [linearIndepOn_iff] at hli
  set l : Finset ℕ →₀ K := Finsupp.onFinset ((Ico 1 n).powerset)
    (fun S => if S ∈ (Ico 1 n).powerset then a S - b S else 0)
    (fun S hS => by by_contra hc; simp [hc] at hS) with hl
  have hlval : ∀ S : Finset ℕ, S ∈ (Ico 1 n).powerset → l S = a S - b S := by
    intro S hS
    rw [hl, Finsupp.onFinset_apply, ite_eq_left hS]
  have hsupp : ∀ S ∈ l.support, S ∈ (Ico 1 n).powerset := by
    intro S hS
    rw [Finsupp.mem_support_iff, hl, Finsupp.onFinset_apply] at hS
    by_contra hc
    simp [hc] at hS
  have hzero : Finsupp.linearCombination K (gessel K n) l = 0 := by
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset l hsupp _ (fun S _ => by simp),
      Finset.sum_congr rfl fun S hS => by rw [hlval S hS, sub_smul],
      Finset.sum_sub_distrib, h, sub_self]
  have hl0 := hli l ((Finsupp.mem_supported K l).2 fun S hS => mem_powerset.1 (hsupp S hS)) hzero
  intro S hS
  have h0 : l S = 0 := by rw [hl0]; rfl
  rw [hlval S hS] at h0
  exact sub_eq_zero.1 h0

/-! ### One degree at a time -/

section Component

variable {K : Type*} [CommRing K] [Algebra ℚ K] {ι : Lambda K →ₐ[K] AlphabetSeries K}

/-- The symmetric functions whose degree-`d` canonical fundamental expansion the involution
complements: those admitting *one* family of coefficients that expands both `ι f` and `ι(ω f)`, the
second with every descent set complemented. Two such witnesses add and scale, so this is a
submodule, and that is what lets `HJO.Sym.lambdaComp_le_completeHomogCompSpan` reduce the statement
to the generators `h_α`. -/
noncomputable def omegaCompat (ι : Lambda K →ₐ[K] AlphabetSeries K) (d : ℕ) :
    Submodule K (Lambda K) where
  carrier := {f | ∃ c : Finset ℕ → K,
    ι f = ∑ T ∈ (Ico 1 d).powerset, c T • gessel K d T ∧
      ι (omegaStd K f) = ∑ T ∈ (Ico 1 d).powerset, c T • gessel K d (Ico 1 d \ T)}
  add_mem' := by
    rintro f g ⟨c, h1, h2⟩ ⟨c', h1', h2'⟩
    refine ⟨c + c', ?_, ?_⟩
    · rw [map_add, h1, h1', ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun T _ => (add_smul _ _ _).symm
    · rw [map_add, map_add, h2, h2', ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun T _ => (add_smul _ _ _).symm
  zero_mem' := ⟨0, by simp, by simp⟩
  smul_mem' := by
    rintro r f ⟨c, h1, h2⟩
    refine ⟨r • c, ?_, ?_⟩
    · rw [map_smul, h1, Finset.smul_sum]
      exact Finset.sum_congr rfl fun T _ => by rw [Pi.smul_apply, smul_assoc]
    · rw [map_smul, map_smul, h2, Finset.smul_sum]
      exact Finset.sum_congr rfl fun T _ => by rw [Pi.smul_apply, smul_assoc]

omit [Algebra ℚ K] in
/-- **Grouping a sum over permutations by the inverse descent set.** Each subset of the window
contributes as many times as there are permutations with that inverse descent set. -/
theorem sum_perm_eq_sum_powerset {d : ℕ} (A : Finset (Equiv.Perm (Fin d)))
    (G : Finset ℕ → AlphabetSeries K) :
    ∑ σ ∈ A, G (invDescentSet σ)
      = ∑ T ∈ (Ico 1 d).powerset, ((#{σ ∈ A | invDescentSet σ = T} : ℕ) : K) • G T := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun σ : Equiv.Perm (Fin d) => invDescentSet σ)
    (t := (Ico 1 d).powerset) (fun σ _ => mem_powerset.2 (invDescentSet_subset_Ico σ))
    (fun σ => G (invDescentSet σ))]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Nat.cast_smul_eq_nsmul, ← Finset.sum_const]
  exact Finset.sum_congr rfl fun σ hσ => by rw [(mem_filter.1 hσ).2]

/-- **A complete homogeneous product is compatible.**
`HJO.ParkingFunctions.realisation_completeHomogComp` and
`HJO.ParkingFunctions.realisation_elemSymmComp` expand `h_α` and `e_α = ω(h_α)` over the *same*
permutations, so grouping both by the inverse descent set produces one family of coefficients
serving for both. -/
theorem completeHomogComp_mem_omegaCompat (hι : IsRealisation ι) {d : ℕ} {α : List ℕ}
    (hα : α.sum = d) : completeHomogComp K α ∈ omegaCompat ι d := by
  classical
  refine ⟨fun T => ((#{σ ∈ {σ : Equiv.Perm (Fin d) | permDescentSet σ ⊆ compDescent α} |
      invDescentSet σ = T} : ℕ) : K), ?_, ?_⟩
  · rw [realisation_completeHomogComp hι hα]
    exact sum_perm_eq_sum_powerset _ fun T => gessel K d T
  · rw [omegaStd_completeHomogComp, realisation_elemSymmComp hι hα]
    exact sum_perm_eq_sum_powerset _ fun T => gessel K d (Ico 1 d \ T)

/-- Every symmetric function of degree `d` is compatible: the graded piece is spanned by the
complete homogeneous products of compositions of `d`. -/
theorem lambdaComp_le_omegaCompat (hι : IsRealisation ι) (d : ℕ) :
    LambdaComp K d ≤ omegaCompat ι d := by
  refine le_trans (lambdaComp_le_completeHomogCompSpan K d) ?_
  rw [completeHomogCompSpan]
  refine Submodule.span_le.2 ?_
  rintro f ⟨α, -, hsum, rfl⟩
  exact completeHomogComp_mem_omegaCompat hι hsum

/-- **The involution complements a canonical expansion in one
degree.** For `f ∈ Λ_d` with `ι f = ∑_T c_T F_{d,T}`, the involution gives
`ι(ω f) = ∑_T c_T F_{d,\{1,…,d-1\}∖T}`.

`f` is compatible, so *some* family witnesses both expansions; the fundamentals are linearly
independent, so that family is the given one. -/
@[hjo "lem_om_omega_expansion_component"]
theorem realisation_omegaStd_of_component (hι : IsRealisation ι) {d : ℕ} (c : Finset ℕ → K)
    {f : Lambda K} (hf : f ∈ LambdaComp K d)
    (hexp : ι f = ∑ T ∈ (Ico 1 d).powerset, c T • gessel K d T) :
    ι (omegaStd K f) = ∑ T ∈ (Ico 1 d).powerset, c T • gessel K d (Ico 1 d \ T) := by
  obtain ⟨c₀, h1, h2⟩ := lambdaComp_le_omegaCompat hι d hf
  have hc := eq_of_sum_gessel_eq K (hexp.symm.trans h1)
  rw [h2]
  exact Finset.sum_congr rfl fun T hT => by rw [hc T hT]

end Component

/-! ### All degrees at once, and an arbitrary index set -/

section Canonical

variable {L : Type*} [Field L] [Algebra ℚ L] {ι : Lambda L →ₐ[L] AlphabetSeries L}

/-- **The involution conjugates a canonical descent expansion.**
For `ι f = ∑_S a_S F_{n,S}` over the subsets `S` of the window,
`ι(ω f) = ∑_S a_S F_{n,(\{1,…,n-1\}∖S)^{∨n}}`.

Split `f` into homogeneous components. A monomial of `ι(f_d)` has total degree `d` and a monomial of
the right-hand side has total degree `n`, so `ι(f_d) = 0` for `d ≠ n` and `ι(f_n)` carries the whole
expansion. `HJO.ParkingFunctions.realisation_omegaStd_of_component` applies in each degree — with
the zero family off `n` — and `HJO.gessel_reverse_sum` turns the complement into the conjugate. -/
@[hjo "lem_om_gessel_omega_canonical"]
theorem realisation_omegaStd_canonical (hι : IsRealisation ι) {n : ℕ} (a : Finset ℕ → L)
    {f : Lambda L} (hf : ι f = ∑ S ∈ (Ico 1 n).powerset, a S • gessel L n S) :
    ι (omegaStd L f)
      = ∑ S ∈ (Ico 1 n).powerset, a S • gessel L n (descentReverse n (Ico 1 n \ S)) := by
  classical
  set M := max (weightedTotalDegree (fun i => i + 1) f + 1) (n + 1) with hM
  set fc : ℕ → Lambda L := fun d => weightedHomogeneousComponent (fun i => i + 1) d f with hfc
  have hnM : n ∈ range M := mem_range.2 (lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right _ _))
  have hdecomp : ∑ d ∈ range M, fc d = f := by
    rw [← sum_weightedHomogeneousComponent_range f]
    refine (Finset.sum_subset (fun d hd =>
      mem_range.2 (lt_of_lt_of_le (mem_range.1 hd) (le_max_left _ _))) ?_).symm
    intro d _ hd
    rw [hfc]
    exact weightedHomogeneousComponent_eq_zero _ _ (by rw [mem_range] at hd; omega)
  have hcoeff : ∀ d ∈ range M, ∀ α : ℕ →₀ ℕ, degHom α = d →
      MvPowerSeries.coeff α (ι (fc d)) = MvPowerSeries.coeff α (ι f) := by
    intro d hd α hα
    conv_rhs => rw [← hdecomp]
    rw [map_sum, map_sum, Finset.sum_eq_single_of_mem d hd]
    intro e _ hne
    refine by_contra fun hc => hne ?_
    exact (degHom_of_coeff_iota_ne_zero hι
      (weightedHomogeneousComponent_mem _ f e) hc).symm.trans hα
  have hgesselcoeff : ∀ α : ℕ →₀ ℕ, degHom α ≠ n →
      MvPowerSeries.coeff α (∑ S ∈ (Ico 1 n).powerset, a S • gessel L n S) = 0 := by
    intro α hα
    rw [map_sum]
    exact Finset.sum_eq_zero fun S _ => by
      rw [map_smul, coeff_gessel_eq_zero_of_degHom_ne L hα, smul_zero]
  have hcomp0 : ∀ d ∈ range M, d ≠ n → ι (fc d) = 0 := by
    intro d hd hdn
    refine MvPowerSeries.ext fun α => ?_
    rw [map_zero]
    by_cases hα : degHom α = d
    · rw [hcoeff d hd α hα, hf, hgesselcoeff α fun hc => hdn (hα.symm.trans hc)]
    · exact by_contra fun hc => hα (degHom_of_coeff_iota_ne_zero hι
        (weightedHomogeneousComponent_mem _ f d) hc)
  have hcompn : ι (fc n) = ∑ S ∈ (Ico 1 n).powerset, a S • gessel L n S := by
    refine MvPowerSeries.ext fun α => ?_
    by_cases hα : degHom α = n
    · rw [hcoeff n hnM α hα, hf]
    · rw [hgesselcoeff α hα]
      exact by_contra fun hc => hα (degHom_of_coeff_iota_ne_zero hι
        (weightedHomogeneousComponent_mem _ f n) hc)
  have homega : ι (omegaStd L f) = ι (omegaStd L (fc n)) := by
    conv_lhs => rw [← hdecomp]
    rw [map_sum, map_sum, Finset.sum_eq_single_of_mem n hnM]
    intro e he hne
    have h0 := realisation_omegaStd_of_component hι (0 : Finset ℕ → L)
      (weightedHomogeneousComponent_mem _ f e) (by rw [hcomp0 e he hne]; simp)
    rw [h0]
    simp
  have hn := realisation_omegaStd_of_component hι a
    (weightedHomogeneousComponent_mem _ f n) hcompn
  exact HJO.gessel_reverse_sum ι hι n (Finset ℕ) ((Ico 1 n).powerset) a (fun S => Ico 1 n \ S)
    (fun S _ => sdiff_subset) (omegaStd L f) (homega.trans hn)

/-- **The involution conjugates the descent sets.** The same statement
at an arbitrary finite index set: for `ι f = ∑_{i ∈ s} w_i F_{n,S_i}`,
`ι(ω f) = ∑_{i ∈ s} w_i F_{n,(\{1,…,n-1\}∖S_i)^{∨n}}`.

Grouping the index set by the value of `S_i` turns the hypothesis into a canonical expansion and the
conclusion into the canonical conclusion; the *same* regrouping serves on both sides, so the
injectivity of `T ↦ (\{1,…,n-1\}∖T)^{∨n}` that the route needs is not used. -/
@[hjo "lem_gessel_omega_conjugate"]
theorem realisation_omegaStd_conjugate (hι : IsRealisation ι) (n : ℕ) (I : Type) (s : Finset I)
    (w : I → L) (S : I → Finset ℕ) (hS : ∀ i ∈ s, S i ⊆ Ico 1 n) {f : Lambda L}
    (hf : ι f = ∑ i ∈ s, w i • gessel L n (S i)) :
    ι (omegaStd L f) = ∑ i ∈ s, w i • gessel L n (descentReverse n (Ico 1 n \ S i)) := by
  classical
  have hgroup : ∀ G : Finset ℕ → AlphabetSeries L,
      ∑ i ∈ s, w i • G (S i)
        = ∑ T ∈ (Ico 1 n).powerset, (∑ i ∈ s.filter fun i => S i = T, w i) • G T := by
    intro G
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun i => S i) (t := (Ico 1 n).powerset)
      (fun i hi => mem_powerset.2 (hS i hi)) (fun i => w i • G (S i))]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun i hi => by rw [(mem_filter.1 hi).2]
  rw [hgroup fun T => gessel L n (descentReverse n (Ico 1 n \ T))]
  exact realisation_omegaStd_canonical hι _ (hf.trans (hgroup fun T => gessel L n T))

/-- **The involution complements the descent sets.** The conjugate form of
the previous lemma with the reversal discarded: on `Λ` the reversal is invisible, which is
`HJO.gessel_reverse_sum` applied once more, and `HJO.ParkingFunctions.descentReverse_descentReverse`
undoes it. -/
@[hjo "lem_gessel_omega_complement"]
theorem realisation_omegaStd_complement (hι : IsRealisation ι) (n : ℕ) (I : Type) (s : Finset I)
    (w : I → L) (S : I → Finset ℕ) (hS : ∀ i ∈ s, S i ⊆ Ico 1 n) {f : Lambda L}
    (hf : ι f = ∑ i ∈ s, w i • gessel L n (S i)) :
    ι (omegaStd L f) = ∑ i ∈ s, w i • gessel L n (Ico 1 n \ S i) := by
  have h1 := realisation_omegaStd_conjugate hι n I s w S hS hf
  have h2 := HJO.gessel_reverse_sum ι hι n I s w (fun i => descentReverse n (Ico 1 n \ S i))
    (fun i _ => descentReverse_subset_Ico sdiff_subset) (omegaStd L f) h1
  rw [h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [descentReverse_descentReverse (sdiff_subset.trans Ico_subset_Iic_self)]

/-- **Negating the alphabet complements the descent sets.** For
`ι f = ∑_{i ∈ s} c_i F_{n,D_i}`,
`ι(ω₋ f) = (-1)^n ∑_{i ∈ s} c_i F_{n,\{1,…,n-1\}∖D_i}`.

`ω₋` is `ω` followed by the scaling of the alphabet by `-1`
(`HJO.Sym.plethNegate_eq_plethScale_omegaStd`), a realisation turns that into the negation of the
letters (`HJO.Sym.realisation_plethScale_neg_one`), and negating the
letters of a fundamental of degree `n` multiplies it by `(-1)^n`
(`HJO.ParkingFunctions.letterNegate_gessel`). -/
@[hjo "lem_cm_omega_gessel"]
theorem realisation_plethNegate_gessel (hι : IsRealisation ι) (n : ℕ) (I : Type) (s : Finset I)
    (c : I → L) (D : I → Finset ℕ) (hD : ∀ i ∈ s, D i ⊆ Ico 1 n) {f : Lambda L}
    (hf : ι f = ∑ i ∈ s, c i • gessel L n (D i)) :
    ι (plethNegate L f) = ((-1 : L) ^ n) • ∑ i ∈ s, c i • gessel L n (Ico 1 n \ D i) := by
  have h1 := realisation_omegaStd_complement hι n I s c D hD hf
  rw [plethNegate_eq_plethScale_omegaStd, realisation_plethScale_neg_one hι, h1, map_sum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, letterNegate_gessel, smul_comm]

end Canonical

end HJO.ParkingFunctions
