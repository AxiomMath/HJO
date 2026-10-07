/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.SignExtraction.GesselIndependent
public meta import HJO.Attr

/-! # The coefficients of a fundamental expansion are determined

Two expansions in Gessel's fundamental quasisymmetric functions `F_{n,S}` that name the same series
have the same coefficients. The expansions are not assumed to be indexed by the sets of steps
themselves: each side is an arbitrary finite family, so the same set of steps may occur many times,
and the statement is that for every set of steps `T` the *total* coefficient of `F_{n,T}` — the sum
of the scalars over the indices naming `T` — agrees on the two sides.

The proof is the standard one. Each side is regrouped over the fibres of its indexing map, which
turns both into combinations indexed by one common finite set of sets of steps, and subtracting
leaves a relation whose scalars are the differences of the total coefficients. The linear
independence of the fundamentals, `HJO.ParkingFunctions.linearIndepOn_gessel`, kills those scalars.

## Main results

* `HJO.ParkingFunctions.sum_smul_gessel_eq_sum_fiberwise`: a finite combination of fundamentals
  regrouped over the fibres of its indexing map, as a combination indexed by any finite set of sets
  of steps containing the map's image.
* `HJO.ParkingFunctions.sum_filter_eq_sum_filter_of_sum_smul_gessel_eq`: two finite combinations of
  fundamentals with equal value have equal total coefficient at every set of steps inside the
  window `{1, …, n-1}`.

## Implementation notes

The two index sets are `Finset`s in arbitrary types, which is the "finite sets" and
also what the regrouping needs; the coefficients `c` and `c'` are total functions on those types,
only their values on the index sets mattering. The scalar multiple is `•` for the `K`-module
structure on `HJO.Sym.AlphabetSeries K`, the one the independence statement is phrased in.

Both the hypotheses `S i ⊆ Finset.Ico 1 n` and the restriction `T ⊆ Finset.Ico 1 n` on the
conclusion are necessary, and for the same reason the index set of `linearIndepOn_gessel` is the
window: `gessel` is total in `S`, and a step outside the window constrains only the auxiliary
sequence beyond the `n` positions a word occupies, so distinct such sets can name the same series.
Already `gessel K 2 {5} = gessel K 2 ∅`, so dropping the hypothesis on `S` makes the conclusion
false at `T = ∅`, and dropping it on `T` makes it false at `T = {5}`.

The `n ≥ 1` is dead, as it is for the independence: at `n = 0` the window is empty, the
only set of steps inside it is `∅`, and the statement is the tautology that the two sides of a
relation between multiples of `F_{0,∅} = 1` have equal total coefficient.

The bridge from the bundled `LinearIndepOn` to a `Finset`-indexed relation is Mathlib's
`linearIndepOn_iff'`. No hypothesis relates the two index sets, and no cardinality or injectivity
assumption is made on `S` or `S'`; the fibrewise regrouping absorbs all repetition.

## References

The lemma `HJO.ParkingFunctions.sum_filter_eq_sum_filter_of_sum_smul_gessel_eq` is the consumable
form of `HJO.ParkingFunctions.linearIndepOn_gessel`. -/

@[expose] public section

open Finset

namespace HJO.ParkingFunctions

/-- **Regrouping a combination of fundamentals by set of steps**: a finite combination
`∑_{i ∈ I} c_i F_{n,S_i}` of Gessel fundamental quasisymmetric functions, rewritten as a
combination indexed by any finite set `A` of sets of steps containing every `S_i`, the coefficient
of `F_{n,T}` being the total `∑_{i ∈ I, S_i = T} c_i` over the fibre of `T`. -/
theorem sum_smul_gessel_eq_sum_fiberwise {K : Type*} [CommRing K] {ι : Type*} {n : ℕ}
    (I : Finset ι) (c : ι → K) (S : ι → Finset ℕ) {A : Finset (Finset ℕ)}
    (hA : ∀ i ∈ I, S i ∈ A) :
    ∑ i ∈ I, c i • gessel K n (S i) = ∑ T ∈ A, (∑ i ∈ I with S i = T, c i) • gessel K n T := by
  rw [← Finset.sum_fiberwise_of_maps_to hA fun i => c i • gessel K n (S i)]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.sum_smul]
  exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]

/-- **The coefficients of a fundamental expansion are determined**: if two finite combinations of
Gessel fundamental quasisymmetric functions whose sets of steps all lie inside the window
`{1, …, n-1}` name the same series, then for every set of steps `T` inside that window the total
coefficient of `F_{n,T}` is the same on both sides. Neither indexing map is assumed injective, so
the total coefficient — the sum of the scalars over the indices naming `T` — is the right invariant;
the restriction of `T` to the window cannot be dropped, since outside it `F_{n,T}` is a
totalization and distinct sets name the same series. -/
@[hjo "lem_cm_gessel_coeff_unique"]
theorem sum_filter_eq_sum_filter_of_sum_smul_gessel_eq {K : Type*} [CommRing K] {ι κ : Type*}
    {n : ℕ} {I : Finset ι} {J : Finset κ} {c : ι → K} {c' : κ → K} {S : ι → Finset ℕ}
    {S' : κ → Finset ℕ} (hS : ∀ i ∈ I, S i ⊆ Ico 1 n) (hS' : ∀ j ∈ J, S' j ⊆ Ico 1 n)
    (hsum : ∑ i ∈ I, c i • gessel K n (S i) = ∑ j ∈ J, c' j • gessel K n (S' j))
    {T : Finset ℕ} (hT : T ⊆ Ico 1 n) :
    ∑ i ∈ I with S i = T, c i = ∑ j ∈ J with S' j = T, c' j := by
  obtain ⟨A, hAT, hAI, hAJ, hAsub⟩ : ∃ A : Finset (Finset ℕ), T ∈ A ∧ (∀ i ∈ I, S i ∈ A) ∧
      (∀ j ∈ J, S' j ∈ A) ∧ (A : Set (Finset ℕ)) ⊆ {U : Finset ℕ | U ⊆ Ico 1 n} := by
    refine ⟨insert T (I.image S ∪ J.image S'), mem_insert_self _ _,
      fun i hi => mem_insert_of_mem (mem_union_left _ (mem_image_of_mem S hi)),
      fun j hj => mem_insert_of_mem (mem_union_right _ (mem_image_of_mem S' hj)), fun U hU => ?_⟩
    change U ⊆ Ico 1 n
    rcases mem_insert.mp (mem_coe.mp hU) with rfl | hU'
    · exact hT
    · rcases mem_union.mp hU' with h | h
      · obtain ⟨i, hi, rfl⟩ := mem_image.mp h
        exact hS i hi
      · obtain ⟨j, hj, rfl⟩ := mem_image.mp h
        exact hS' j hj
  have hzero : ∑ U ∈ A, ((∑ i ∈ I with S i = U, c i) - ∑ j ∈ J with S' j = U, c' j) •
      gessel K n U = 0 := by
    rw [Finset.sum_congr rfl fun U _ => sub_smul _ _ (gessel K n U), Finset.sum_sub_distrib,
      ← sum_smul_gessel_eq_sum_fiberwise I c S hAI,
      ← sum_smul_gessel_eq_sum_fiberwise J c' S' hAJ, hsum, sub_self]
  exact sub_eq_zero.mp (linearIndepOn_iff'.mp (linearIndepOn_gessel K n) A
    (fun U => (∑ i ∈ I with S i = U, c i) - ∑ j ∈ J with S' j = U, c' j) hAsub hzero T hAT)

end HJO.ParkingFunctions
