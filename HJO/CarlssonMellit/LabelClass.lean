/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.Runs
public import HJO.CarlssonMellit.Tuples
public meta import HJO.Attr

/-! # Transposing two labels, and the classes of labellings it matches

Interchanging the two consecutive labels `m`, `m + 1` everywhere — the relabelling `τ_m` of
`HJO.Dyck.transposeTuple` — carries the no-attack labellings of a partial Dyck path with
prescription `σ` bijectively onto those with prescription `τ_m σ`, and it does so class by class:
two labellings lie in the same class when they have the same two-letter support and agree off it,
and `τ_m` changes neither the support nor the letters off it. This file proves those statements,
which are what let the swapping proposition be checked one class at a time.

## Main definitions

* `HJO.Dyck.labelClass`: `K_m(π, σ, w)`, the class of the labelling `w`.

## Main results

* `HJO.Dyck.transposeTuple_lt_and_injective`: `τ_m` carries a listing of the labels of a level to
  another such listing, and always preserves distinctness.
* `HJO.Dyck.bijOn_transposeTuple`: `τ_m` is a bijection from `U(π, σ)` onto `U(π, τ_m σ)`.
* `HJO.Dyck.equivalence_labelClass`: the classes partition `U(π, σ)`.
* `HJO.Dyck.bijOn_transposeTuple_labelClass`: `τ_m` matches the class of `w` for `σ` with the class
  of `τ_m w` for `τ_m σ`.

## Implementation notes

*`bijOn_transposeTuple` needs no hypothesis on `σ`.* In Carlsson and Mellit the bijection assumes
the entries of `σ` pairwise distinct, because their `U(π, σ)` is only *defined* under that
assumption; `HJO.Dyck.noAttackLabellings` is defined for every tuple, deriving distinctness where it
is needed instead, so the bijection holds outright. The separate step "the target set is defined,
because `τ_m σ` has distinct entries" is therefore vacuous here, and the distinctness statement it
invokes is `HJO.Dyck.transposeTuple_injective` below, stated for its own sake.

*Positions of a class are compared through `HJO.Dyck.labelSupport`*, a `Finset ℕ`, while a labelling
is a tuple `Fin N → ℕ`; the condition "`w'_i = w_i` for every `i ∉ S_m(w)`" is read at the positions
`i : Fin N` whose value `(i : ℕ)` is outside that `Finset`. Positions at or above `N` are not
labelled at all, so nothing is lost.

*The classes are stated to be an equivalence relation on the subtype `↥U(π, σ)`*, which is the
"equivalence relation on `U(π, σ)`" of Carlsson and Mellit: reflexivity and symmetry both need the
labelling compared against to lie in `U(π, σ)`, and carrying that as a subtype is what makes
`Equivalence` applicable.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 4.
-/

@[expose] public section

open Finset

namespace HJO.Dyck

open HJO.Sym

/-! ### The transposition of two consecutive letters -/

/-- The transposition of the two consecutive letters `m`, `m + 1` fixes every other letter. -/
theorem swap_succ_of_ne {m a : ℕ} (h : a ≠ m) (h' : a ≠ m + 1) : Equiv.swap m (m + 1) a = a :=
  Equiv.swap_apply_of_ne_of_ne h h'

/-- A letter lies in `{m, m + 1}` exactly when its image under the transposition of `m` and `m + 1`
does: the transposition preserves the pair it interchanges. This is what makes the two-letter
support invariant under the relabelling. -/
theorem swap_succ_mem_pair_iff {m a : ℕ} :
    (Equiv.swap m (m + 1) a = m ∨ Equiv.swap m (m + 1) a = m + 1) ↔ (a = m ∨ a = m + 1) := by
  by_cases h : a = m
  · subst h; simp
  by_cases h' : a = m + 1
  · subst h'; simp [Equiv.swap_apply_right]
  · rw [swap_succ_of_ne h h']

/-! ### Transposing a tuple of labels -/

variable {N k : ℕ}

/-- **Transposing preserves distinctness**: the entries of `τ_m σ` are pairwise distinct whenever
those of `σ` are, the relabelling being an injection of the letters. -/
@[hjo "lem_cm_transposetuple_distinct"]
theorem transposeTuple_injective {ι : Type*} (m : ℕ) {σ : ι → ℕ} (h : Function.Injective σ) :
    Function.Injective (transposeTuple m σ) :=
  (Equiv.swap m (m + 1)).injective.comp h

/-- **Transposing preserves a permutation tuple**: if the entries of `σ` are the labels
`0, …, k-1` of the level, each exactly once, then so are those of `τ_m σ` — provided both `m` and
`m + 1` are labels of the level, which is Carlsson and Mellit's `m ≤ k-1`. The transposition is
then a bijection of the labels, and a bijection carries a listing without repetition to another
one.

A listing of the labels without repetition is recorded as the pair of conditions "every entry is a
label" and "the entries are pairwise distinct"; for a tuple of `k` labels these are equivalent to
listing all of them. The hypothesis `m + 1 < k` is essential: without it `τ_m σ` has an entry equal
to `k`, and the conclusion is false. -/
@[hjo "lem_cm_transposetuple_perm"]
theorem transposeTuple_lt_and_injective {m : ℕ} {σ : Fin k → ℕ} (hm : m + 1 < k)
    (hlt : ∀ i, σ i < k) (hinj : Function.Injective σ) :
    (∀ i, transposeTuple m σ i < k) ∧ Function.Injective (transposeTuple m σ) := by
  refine ⟨fun i => ?_, transposeTuple_injective m hinj⟩
  by_cases h : σ i = m
  · simpa [transposeTuple, h] using hm
  by_cases h' : σ i = m + 1
  · simpa [transposeTuple, h', Equiv.swap_apply_right] using Nat.lt_of_succ_lt hm
  · simpa [transposeTuple, swap_succ_of_ne h h'] using hlt i

/-! ### Transposing the labellings of a path -/

variable {x : Fin N → ℕ} {σ : Fin k → ℕ} {m : ℕ} {w : Fin N → ℕ}

/-- The relabelling on labellings, at one position. -/
theorem transposeTuple_apply (m : ℕ) (w : Fin N → ℕ) (i : Fin N) :
    transposeTuple m w i = Equiv.swap m (m + 1) (w i) :=
  rfl

/-- **Transposing two labels is a bijection of labellings**: `w ↦ τ_m w` carries `U(π, σ)`
bijectively onto `U(π, τ_m σ)`. It is an involution of the tuples, and it carries the prescription
`σ` to the prescription `τ_m σ` while preserving the no-attack condition, the relabelling being
injective on letters. -/
@[hjo "lem_cm_transposetuple_bijection"]
theorem bijOn_transposeTuple (x : Fin N → ℕ) (σ : Fin k → ℕ) (m : ℕ) :
    Set.BijOn (transposeTuple m) (noAttackLabellings x σ)
      (noAttackLabellings x (transposeTuple m σ)) := by
  have hmaps : ∀ (τ : Fin k → ℕ), Set.MapsTo (transposeTuple m) (noAttackLabellings x τ)
      (noAttackLabellings x (transposeTuple m τ)) := fun τ v hv =>
    ⟨fun i j hij => by
        simp only [transposeTuple, Function.comp_apply]
        rw [eq_of_mem_noAttackLabellings hv hij],
      fun i j hij h => ne_of_mem_noAttackLabellings hv hij
        ((Equiv.swap m (m + 1)).injective h)⟩
  refine ⟨hmaps σ, fun v _ v' _ h => ?_, fun v hv => ⟨transposeTuple m v, ?_, ?_⟩⟩
  · have := congrArg (transposeTuple m) h
    rwa [transposeTuple_transposeTuple, transposeTuple_transposeTuple] at this
  · have := hmaps (transposeTuple m σ) hv
    rwa [transposeTuple_transposeTuple] at this
  · exact transposeTuple_transposeTuple m v

/-- The relabelling does not move the two-letter support: it permutes the pair `{m, m + 1}` and
fixes every letter outside it. -/
@[simp]
theorem labelSupport_transposeTuple (m : ℕ) (w : Fin N → ℕ) :
    labelSupport m (transposeTuple m w) = labelSupport m w := by
  refine Finset.ext fun p => ?_
  simp only [mem_labelSupport]
  refine and_congr_right fun hp => ?_
  rw [wordOfFin_of_lt _ hp, wordOfFin_of_lt _ hp, transposeTuple_apply]
  exact swap_succ_mem_pair_iff

/-- The relabelling does not move the letters outside the two-letter support. -/
theorem transposeTuple_apply_of_notMem (m : ℕ) (w : Fin N → ℕ) {i : Fin N}
    (hi : (i : ℕ) ∉ labelSupport m w) : transposeTuple m w i = w i := by
  have h := ne_and_ne_of_notMem_twoLetterSupport i.isLt hi
  rw [wordOfFin_val] at h
  exact swap_succ_of_ne h.1 h.2

/-! ### The classes of labellings -/

/-- **The class of a labelling** `K_m(π, σ, w)`: the no-attack labellings with the same two-letter
support as `w` that agree with `w` outside it. Inside the support the letters may be rearranged
between `m` and `m + 1` in any way the no-attack condition permits, and outside it nothing moves. -/
@[hjo "def_cm_class"]
def labelClass (x : Fin N → ℕ) (σ : Fin k → ℕ) (m : ℕ) (w : Fin N → ℕ) : Set (Fin N → ℕ) :=
  {w' | w' ∈ noAttackLabellings x σ ∧ labelSupport m w' = labelSupport m w ∧
    ∀ i : Fin N, (i : ℕ) ∉ labelSupport m w → w' i = w i}

theorem mem_labelClass {w' : Fin N → ℕ} :
    w' ∈ labelClass x σ m w ↔ w' ∈ noAttackLabellings x σ ∧
      labelSupport m w' = labelSupport m w ∧
        ∀ i : Fin N, (i : ℕ) ∉ labelSupport m w → w' i = w i :=
  Iff.rfl

/-- A labelling lies in its own class. -/
theorem mem_labelClass_self (hw : w ∈ noAttackLabellings x σ) : w ∈ labelClass x σ m w :=
  ⟨hw, rfl, fun _ _ => rfl⟩

/-- Every member of a class is a no-attack labelling. -/
theorem labelClass_subset : labelClass x σ m w ⊆ noAttackLabellings x σ := fun _ h => h.1

/-- **The classes partition the labellings**: lying in a common class is an equivalence relation on
`U(π, σ)`. Reflexivity is immediate; the two conditions defining a class are symmetric in the two
labellings once the supports are known equal, and transitivity chains the two equalities. -/
@[hjo "lem_cm_class_equiv"]
theorem equivalence_labelClass (x : Fin N → ℕ) (σ : Fin k → ℕ) (m : ℕ) :
    Equivalence fun v v' : ↥(noAttackLabellings x σ) =>
      (v' : Fin N → ℕ) ∈ labelClass x σ m (v : Fin N → ℕ) where
  refl v := mem_labelClass_self v.2
  symm {v _} h := ⟨v.2, h.2.1.symm, fun i hi => (h.2.2 i (h.2.1 ▸ hi)).symm⟩
  trans {_ _ c} h h' :=
    ⟨c.2, h'.2.1.trans h.2.1, fun i hi => (h'.2.2 i (h.2.1 ▸ hi)).trans (h.2.2 i hi)⟩

/-- **Transposing two labels matches the classes**: `w' ↦ τ_m w'` carries `K_m(π, σ, w)` bijectively
onto `K_m(π, τ_m σ, τ_m w)`. It is a bijection of the ambient labellings, it does not move the
two-letter support, and it does not move the letters outside it, so both conditions defining a class
are preserved in each direction. -/
@[hjo "lem_cm_class_transpose"]
theorem bijOn_transposeTuple_labelClass (x : Fin N → ℕ) (σ : Fin k → ℕ) (m : ℕ) (w : Fin N → ℕ) :
    Set.BijOn (transposeTuple m) (labelClass x σ m w)
      (labelClass x (transposeTuple m σ) m (transposeTuple m w)) := by
  have hmaps : ∀ (τ : Fin k → ℕ) (v : Fin N → ℕ), Set.MapsTo (transposeTuple m)
      (labelClass x τ m v) (labelClass x (transposeTuple m τ) m (transposeTuple m v)) :=
    fun τ v v' hv' => by
      refine ⟨(bijOn_transposeTuple x τ m).mapsTo hv'.1, ?_, fun i hi => ?_⟩
      · rw [labelSupport_transposeTuple, labelSupport_transposeTuple, hv'.2.1]
      · rw [labelSupport_transposeTuple] at hi
        rw [transposeTuple_apply, transposeTuple_apply, hv'.2.2 i hi]
  refine ⟨hmaps σ w, fun v _ v' _ h => ?_, fun v hv => ⟨transposeTuple m v, ?_, ?_⟩⟩
  · have := congrArg (transposeTuple m) h
    rwa [transposeTuple_transposeTuple, transposeTuple_transposeTuple] at this
  · have := hmaps (transposeTuple m σ) (transposeTuple m w) hv
    rwa [transposeTuple_transposeTuple, transposeTuple_transposeTuple] at this
  · exact transposeTuple_transposeTuple m v

end HJO.Dyck
