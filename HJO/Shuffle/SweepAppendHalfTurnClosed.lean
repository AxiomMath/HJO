/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepAppendPairing

/-! # The half-turn closure of the base paths, and why no larger index set decides the append
identity

`HJO.Mellit.SweepAppend` is, by `HJO.Mellit.sweepAppend_iff_sum_appendDisc`, the vanishing of
`∑_z HJO.Mellit.appendDisc q u a b α A z` over the base paths
`HJO.Mellit.aboveReturnPaths a b α.sum α`. The per-path reading is false, and so is every
refinement of it *inside* that index set: `HJO/Shuffle/SweepAppendBandPerPath.lean` and
`HJO/Shuffle/SweepAppendPairing.lean` record, at ten instances and in two independently written
transcriptions, that the discrepancies are nonzero, pairwise distinct up to sign, and span a space
of dimension one less than their number with the relations spanned by the all-ones vector alone.

The one shape those computations leave open is a **larger** index set. `HJO.Paths.halfTurn` is the
library's only involution of the path type, and it is the obvious candidate: it maps the base
paths *out* of their own set (`HJO.Mellit.halfTurn_notMem_aboveReturnPaths`), so no pairing lives
inside, but the union of the base paths with their half-turn images **is** closed under it. This
file builds that set and settles the question.

## What this file proves

* `HJO.Paths.ht_halfTurn_appendHeights` — **the half turn reverses the concatenation**:
  `halfTurn (z ++ w) = (halfTurn w) ++ (halfTurn z)`, read on heights because the two sides live
  over `N + A` and `A + N`. So the half turn conjugates the **append** recursion into a **prepend**
  recursion, for which the library has no counterpart: the mirror half of the closure carries a
  different identity, and its total is a second unknown rather than something the existing
  machinery computes.
  This is why the half turn transports nothing, and it is the mechanism behind the rest of the file.
* `HJO.Mellit.belowReturnPaths` — the mirror index set: the below-diagonal paths of a given return
  composition, the exact image of the base paths under the half turn
  (`HJO.Mellit.belowReturnPaths_reverse_eq_image_halfTurn`), at the **reversed** composition, which
  is what `HJO.Paths.hasAboveReturns_halfTurn` says.
* `HJO.Mellit.halfTurnClosure` — the half-turn-closed index set
  `aboveReturnPaths a b N α ∪ belowReturnPaths a b N α.reverse`, closed under the half turn
  (`HJO.Mellit.halfTurn_mem_halfTurnClosure`), **minimal** among closed supersets of the base paths
  (`HJO.Mellit.halfTurnClosure_subset`), of cardinality exactly twice theirs
  (`HJO.Mellit.card_halfTurnClosure`), and split by
  `HJO.Mellit.sum_halfTurnClosure`: a sum over it is the sum over the base paths plus the sum of the
  half-turn-transported summands.
* **The transversal obstruction.** The two halves are disjoint
  (`HJO.Mellit.disjoint_aboveReturnPaths_belowReturnPaths`), so every half-turn orbit inside the
  closure meets the base paths in *exactly one* point: the base paths are a transversal. Hence a
  pointwise relation between the summand at `z` and the summand at `halfTurn z` relates the sum over
  the base paths to the sum over the mirror half and to nothing else. In the three possible forms:

  - `HJO.Mellit.sum_halfTurnClosure_eq_zero_of_halfTurn_pairing` — a sign-reversing pairing across
    the closure makes the total over the closure vanish **identically**, for *any* summand, and
    `HJO.Mellit.exists_halfTurn_pairing_sum_ne_zero` exhibits a summand satisfying the pairing whose
    total over the base paths is nonzero. So the pairing shape is consistent with the obligation
    failing: it proves nothing. `HJO.Mellit.exists_halfTurn_pairing_forall_sum_ne_zero` frees that
    witness from the index set — it cancels in pairs at **every** path — so the same verdict holds
    for *every* half-turn-closed index set, not just the minimal one.
  - `HJO.Mellit.sum_halfTurnClosure_eq_two_smul` — a half-turn-*invariant* summand has closure total
    twice the base total, so `HJO.Mellit.sum_halfTurnClosure_eq_zero_iff` says the enlarged identity
    is a restatement of the obligation, not a weakening of it.
  - `HJO.Mellit.eq_zero_of_halfTurn_pairing_of_mirror_eq_zero` — the only non-circular combination,
    a pairing together with a mirror half that vanishes, forces the summand to vanish at every base
    path.

* `HJO.Mellit.appendDisc_eq_zero_of_halfTurn_pairing_of_mirror_eq_zero` — that last statement at the
  actual discrepancy. Its conclusion is the hypothesis of
  `HJO.Mellit.sweepAppend_of_forall_path`, which is false. And
  `HJO.Mellit.forall_appendDisc_eq_zero_of_forall_halfTurnClosure` says the term-by-term reading on
  the closure implies the term-by-term reading on the base paths, so it is false a fortiori.

Together: **a half-turn-closed index set exists, is unique and minimal, and does not decide the
obligation.** Term by term it is strictly stronger than a refuted clause; pairwise it is
information-free; invariantly it is the same statement; and the one combination that would give the
obligation implies the refuted clause. No lemma here assumes `HJO.Mellit.SweepAppend`, the path-sum
identity, or a pairing.

## What the model says, and it is model-only

A transcription of the sweep algebra (a computer model, validated by reproducing
`HJO.Mellit.sweepAppend_nil_two_three_one`, `HJO.Mellit.sweepAppend_nil_one_two_two` and the
`decide`-checked geometry of `HJO/Shuffle/SweepAppendNilTwo.lean`) extends the discrepancy to
the mirror half by the same formula and reports, at `(a,b) = (2,3)` with `α = [1]` (two base paths),
`(a,b) = (2,5)` with `α = [1]` (three) and `(a,b) = (2,3)` with `α = [1,1]` (four), each at `A = 1`:

* the mirror discrepancies are nonzero, and at no base path is the mirror discrepancy `±` the
  discrepancy, nor any `ℚ(q,u)`-multiple of it — the half turn does **not** pair them;
* the total over the mirror half is nonzero, and so is the total over the closure: the identity is
  **false** on the half-turn-closed set, in summed form, let alone term by term;
* the only nonempty proper subset of the closure whose discrepancies sum to zero is the set of base
  paths itself — so the closure admits no second grouping either.

None of that is proved here; the statements above are what is proved, and they do not depend on it.

## References

Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*, sections 4 and 6.
-/

@[expose] public section

namespace HJO.Paths

variable {a b N A : ℕ}

/-! ### The half turn reverses the concatenation -/

/-- **The half turn carries `z` extended by `w` to `w`'s half turn extended by `z`'s.** The
concatenation is *reversed*: what was the last block becomes the first.

This is the mechanism behind everything below. The append identity
`HJO.Mellit.sweepAppend_iff_sum_split` is a statement about extending a base path by a **last**
block, and the stage operator `HJO.Mellit.stageTotal` of its right-hand side acts at level `ℓ`, the
top of the tower the base path has built. Under the half turn that becomes a statement about
extending by a **first** block, and there is no such recursion: the mirror half of the half-turn
closure carries a prepend identity, not the append identity. So the half turn does not transport
the discrepancy to anything already known, and the mirror total is a second unknown rather than a
computed quantity — which is what `HJO.Mellit.eq_zero_of_halfTurn_pairing_of_mirror_eq_zero` needs
and does not have.

The hypotheses are the two endpoint conditions every above-diagonal path satisfies: `z` ends at the
corner and `w` starts at the origin. They are exactly what `HJO.Paths.ht_appendHeights_of_ge` needs,
and without them the two sides differ at the single abscissa `r = aA`, where the concatenation seam
sits. The statement is on heights rather than on the vectors themselves because
`Heights a b (N + A)` and `Heights a b (A + N)` are different types. -/
theorem ht_halfTurn_appendHeights {z : Heights a b N} {w : Heights a b A}
    (hz : ht z (a * N) = b * N) (hw : ht w 0 = 0) {r : ℕ} (hr : r ≤ a * (N + A)) :
    ht (halfTurn (appendHeights z w)) r = ht (appendHeights (halfTurn w) (halfTurn z)) r := by
  have hNA : a * (N + A) = a * N + a * A := Nat.mul_add a N A
  have hbNA : b * (N + A) = b * N + b * A := Nat.mul_add b N A
  have hAN : a * (A + N) = a * A + a * N := Nat.mul_add a A N
  rw [ht_halfTurn hr, ht_appendHeights_apply (show r ≤ a * (A + N) by omega)]
  split_ifs with h
  · rw [ht_halfTurn h, ht_appendHeights_of_ge hz hw (by omega)
      (show a * (N + A) - r ≤ a * (N + A) from Nat.sub_le _ _),
      show a * (N + A) - r - a * N = a * A - r by omega]
    have := ht_le_mul w (a * A - r)
    omega
  · rw [ht_appendHeights_of_le (show a * (N + A) - r ≤ a * N by omega),
      ht_halfTurn (show r - a * A ≤ a * N by omega),
      show a * N - (r - a * A) = a * (N + A) - r by omega]
    have := ht_le_mul z (a * (N + A) - r)
    omega

end HJO.Paths

namespace HJO.Mellit

open Finset HJO.Paths HJO.Sweep

variable {a b N : ℕ} {α : List ℕ}

/-! ### The mirror index set -/

/-- The below-diagonal `(aN, bN)`-paths whose return composition is `α`: the mirror of
`HJO.Mellit.aboveReturnPaths` under the half turn, which by `HJO.Paths.hasAboveReturns_halfTurn`
reverses the composition. -/
def belowReturnPaths (a b N : ℕ) (α : List ℕ) : Finset (Paths.Heights a b N) :=
  univ.filter fun y => Paths.IsBelowDiagonal y ∧ Paths.HasReturns α y

theorem mem_belowReturnPaths_iff {y : Heights a b N} :
    y ∈ belowReturnPaths a b N α ↔ HasReturns α y := by
  rw [belowReturnPaths, Finset.mem_filter]
  exact ⟨fun h => h.2.2, fun h => ⟨Finset.mem_univ _, h.1, h⟩⟩

/-- **The half turn carries a base path into the mirror set**, at the reversed composition. -/
theorem halfTurn_mem_belowReturnPaths {z : Heights a b N} (hz : z ∈ aboveReturnPaths a b N α) :
    halfTurn z ∈ belowReturnPaths a b N α.reverse := by
  have hret : HasAboveReturns α z := mem_aboveReturnPaths_iff.1 hz
  have h : HasReturns α.reverse (halfTurn z) :=
    (hasAboveReturns_halfTurn (α := α.reverse) (y := halfTurn z)).1 (by
      simpa [List.reverse_reverse] using hret)
  exact mem_belowReturnPaths_iff.2 h

/-- **The half turn carries the mirror set back to the base paths.** -/
theorem halfTurn_mem_aboveReturnPaths {y : Heights a b N}
    (hy : y ∈ belowReturnPaths a b N α.reverse) : halfTurn y ∈ aboveReturnPaths a b N α := by
  have h : HasAboveReturns α.reverse.reverse (halfTurn y) :=
    (hasAboveReturns_halfTurn (α := α.reverse) (y := y)).2 (mem_belowReturnPaths_iff.1 hy)
  rw [List.reverse_reverse] at h
  exact mem_aboveReturnPaths_iff.2 h

/-- **The mirror set is the half-turn image of the base paths.** -/
theorem belowReturnPaths_reverse_eq_image_halfTurn :
    belowReturnPaths a b N α.reverse = (aboveReturnPaths a b N α).image halfTurn := by
  refine Finset.ext fun y => ⟨fun hy => ?_, fun hy => ?_⟩
  · exact Finset.mem_image.2 ⟨halfTurn y, halfTurn_mem_aboveReturnPaths hy, halfTurn_halfTurn y⟩
  · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
    exact halfTurn_mem_belowReturnPaths hz

/-! ### The half-turn closure of the base paths -/

/-- **The half-turn-closed index set**: the above-diagonal `(aN, bN)`-paths of return composition
`α` together with their half-turn images, which by
`HJO.Mellit.belowReturnPaths_reverse_eq_image_halfTurn` are exactly the below-diagonal paths of the
reversed composition. -/
def halfTurnClosure (a b N : ℕ) (α : List ℕ) : Finset (Paths.Heights a b N) :=
  aboveReturnPaths a b N α ∪ belowReturnPaths a b N α.reverse

theorem aboveReturnPaths_subset_halfTurnClosure :
    aboveReturnPaths a b N α ⊆ halfTurnClosure a b N α :=
  Finset.subset_union_left

theorem belowReturnPaths_subset_halfTurnClosure :
    belowReturnPaths a b N α.reverse ⊆ halfTurnClosure a b N α :=
  Finset.subset_union_right

/-- **The closure is closed under the half turn.** -/
theorem halfTurn_mem_halfTurnClosure {z : Heights a b N} (hz : z ∈ halfTurnClosure a b N α) :
    halfTurn z ∈ halfTurnClosure a b N α := by
  rcases Finset.mem_union.1 hz with h | h
  · exact belowReturnPaths_subset_halfTurnClosure (halfTurn_mem_belowReturnPaths h)
  · exact aboveReturnPaths_subset_halfTurnClosure (halfTurn_mem_aboveReturnPaths h)

/-- **The closure is the smallest half-turn-closed set containing the base paths**, so it is *the*
index set the pairing question is about: there is no other candidate. -/
theorem halfTurnClosure_subset {T : Finset (Paths.Heights a b N)}
    (hAT : aboveReturnPaths a b N α ⊆ T) (hT : ∀ z ∈ T, halfTurn z ∈ T) :
    halfTurnClosure a b N α ⊆ T := by
  intro y hy
  rcases Finset.mem_union.1 hy with h | h
  · exact hAT h
  · have := hT _ (hAT (halfTurn_mem_aboveReturnPaths h))
    rwa [halfTurn_halfTurn] at this

/-! ### The base paths are a transversal of the half-turn orbits in the closure -/

/-- **The two halves of the closure are disjoint**, by
`HJO.Mellit.not_isBelowDiagonal_of_isAboveDiagonal`: outside the degenerate parameters no path is
both above- and below-diagonal. So every half-turn orbit inside the closure meets the base paths in
exactly one point. -/
theorem disjoint_aboveReturnPaths_belowReturnPaths (hab : Nat.Coprime a b) (ha : 1 < a)
    (hN : 0 < N) : Disjoint (aboveReturnPaths a b N α) (belowReturnPaths a b N α.reverse) :=
  Finset.disjoint_left.2 fun _y hy hy' =>
    not_isBelowDiagonal_of_isAboveDiagonal hab ha hN (mem_aboveReturnPaths_iff.1 hy).1
      (mem_belowReturnPaths_iff.1 hy').1

/-- **The closure is exactly twice as large as the set of base paths.** -/
theorem card_halfTurnClosure (hab : Nat.Coprime a b) (ha : 1 < a) (hN : 0 < N) :
    #(halfTurnClosure a b N α) = 2 * #(aboveReturnPaths a b N α) := by
  rw [halfTurnClosure,
    Finset.card_union_of_disjoint (disjoint_aboveReturnPaths_belowReturnPaths hab ha hN),
    belowReturnPaths_reverse_eq_image_halfTurn,
    Finset.card_image_of_injective _ halfTurn_bijective.injective]
  ring

/-- **A sum over the closure is the base sum plus the half-turn-transported base sum.** This is the
transversal statement in the form the obligation needs: nothing beyond the base paths and their
mirror images is being summed, and the mirror summands are indexed by the base paths themselves. -/
theorem sum_halfTurnClosure {M : Type*} [AddCommMonoid M] (hab : Nat.Coprime a b) (ha : 1 < a)
    (hN : 0 < N) (f : Heights a b N → M) :
    ∑ z ∈ halfTurnClosure a b N α, f z
      = ∑ z ∈ aboveReturnPaths a b N α, f z
        + ∑ z ∈ aboveReturnPaths a b N α, f (halfTurn z) := by
  rw [halfTurnClosure,
    Finset.sum_union (disjoint_aboveReturnPaths_belowReturnPaths hab ha hN),
    belowReturnPaths_reverse_eq_image_halfTurn,
    Finset.sum_image fun x _ y _ h => halfTurn_bijective.injective h]

/-! ### The transversal obstruction: the three pointwise shapes, and what each is worth -/

section Obstruction

variable {M : Type*} [AddCommGroup M] [Module ℚ M]

/-- **A sign-reversing pairing across the closure makes the closure total vanish identically.** No
hypothesis on `f` beyond the pairing: the conclusion holds for *every* summand satisfying it, which
is exactly why it carries no information about the base total. -/
theorem sum_halfTurnClosure_eq_zero_of_halfTurn_pairing {M : Type*} [AddCommGroup M]
    (hab : Nat.Coprime a b) (ha : 1 < a) (hN : 0 < N) {f : Heights a b N → M}
    (hf : ∀ z ∈ halfTurnClosure a b N α, f z + f (halfTurn z) = 0) :
    ∑ z ∈ halfTurnClosure a b N α, f z = 0 := by
  rw [sum_halfTurnClosure hab ha hN, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun z hz => hf z (aboveReturnPaths_subset_halfTurnClosure hz)

/-- **The pairing shape proves nothing.** There is a summand on the half-turn closure which cancels
in pairs under the half turn and whose total over the base paths is nonzero. So the hypothesis
"the discrepancies cancel pairwise under the half turn" is *consistent with* the append identity
failing, and a proof of it would not be a proof of `HJO.Mellit.SweepAppend`.

The witness is the indicator of the base paths minus the indicator of the mirror half — the
canonical sign-reversing summand — and the computation is the transversal: the base paths meet each
half-turn orbit once, so the pairing fixes the mirror values from the base ones and constrains the
base values not at all. -/
theorem exists_halfTurn_pairing_sum_ne_zero (hab : Nat.Coprime a b) (ha : 1 < a) (hN : 0 < N)
    (hne : (aboveReturnPaths a b N α).Nonempty) {m : M} (hm : m ≠ 0) :
    ∃ f : Heights a b N → M,
      (∀ z ∈ halfTurnClosure a b N α, f z + f (halfTurn z) = 0) ∧
        ∑ z ∈ aboveReturnPaths a b N α, f z ≠ 0 := by
  classical
  refine ⟨fun z => if z ∈ aboveReturnPaths a b N α then m else -m, fun z hz => ?_, ?_⟩
  · have hdisj := disjoint_aboveReturnPaths_belowReturnPaths (α := α) hab ha hN
    rcases Finset.mem_union.1 hz with h | h
    · have h' : halfTurn z ∉ aboveReturnPaths a b N α := fun hc =>
        (Finset.disjoint_left.1 hdisj hc) (halfTurn_mem_belowReturnPaths h)
      simp [h, h']
    · have h0 : z ∉ aboveReturnPaths a b N α := fun hc =>
        (Finset.disjoint_left.1 hdisj hc) h
      simp [h0, halfTurn_mem_aboveReturnPaths h]
  · have hsum : ∑ z ∈ aboveReturnPaths a b N α,
        (if z ∈ aboveReturnPaths a b N α then m else -m) = #(aboveReturnPaths a b N α) • m := by
      rw [← Finset.sum_const]
      exact Finset.sum_congr rfl fun z hz => by simp [hz]
    rw [hsum, ← Nat.cast_smul_eq_nsmul ℚ]
    exact smul_ne_zero (Nat.cast_ne_zero.2 hne.card_pos.ne') hm

/-- **No half-turn-closed index set at all decides the obligation.** There is a summand on the
*whole* path type which cancels in pairs under the half turn **everywhere** and whose total over the
base paths is nonzero. So for every half-turn-closed `T` — the closure of
`HJO.Mellit.halfTurnClosure`, the union of all above- and below-diagonal paths, the whole type — the
hypothesis "the summands cancel pairwise under the half turn on `T`" is satisfiable with the base
total nonzero, and therefore implies nothing about it. This is
`HJO.Mellit.exists_halfTurn_pairing_sum_ne_zero` with the quantifier freed from any index set, and
it is the statement that closes the shape.

The witness is `m` on the base paths, `-m` on the mirror half and `0` elsewhere. The three cases of
the pairing are the three ways the half turn can move a path: base to mirror, mirror to base, and
neither to neither — the last because the half turn is an involution, so it cannot carry a path
outside the closure into it. -/
theorem exists_halfTurn_pairing_forall_sum_ne_zero (hab : Nat.Coprime a b) (ha : 1 < a)
    (hN : 0 < N) (hne : (aboveReturnPaths a b N α).Nonempty) {m : M} (hm : m ≠ 0) :
    ∃ f : Heights a b N → M,
      (∀ z, f z + f (halfTurn z) = 0) ∧ ∑ z ∈ aboveReturnPaths a b N α, f z ≠ 0 := by
  classical
  have hdisj := disjoint_aboveReturnPaths_belowReturnPaths (α := α) hab ha hN
  refine ⟨fun z => if z ∈ aboveReturnPaths a b N α then m
      else if z ∈ belowReturnPaths a b N α.reverse then -m else 0, fun z => ?_, ?_⟩
  · by_cases h : z ∈ aboveReturnPaths a b N α
    · have h1 : halfTurn z ∉ aboveReturnPaths a b N α := fun hc =>
        (Finset.disjoint_left.1 hdisj hc) (halfTurn_mem_belowReturnPaths h)
      simp [h, h1, halfTurn_mem_belowReturnPaths h]
    · by_cases h' : z ∈ belowReturnPaths a b N α.reverse
      · simp [h, h', halfTurn_mem_aboveReturnPaths h']
      · have h1 : halfTurn z ∉ aboveReturnPaths a b N α := fun hc => h' (by
          simpa using halfTurn_mem_belowReturnPaths hc)
        have h2 : halfTurn z ∉ belowReturnPaths a b N α.reverse := fun hc => h (by
          simpa using halfTurn_mem_aboveReturnPaths hc)
        simp [h, h', h1, h2]
  · have hsum : ∑ z ∈ aboveReturnPaths a b N α, (if z ∈ aboveReturnPaths a b N α then m
        else if z ∈ belowReturnPaths a b N α.reverse then -m else 0)
        = #(aboveReturnPaths a b N α) • m := by
      rw [← Finset.sum_const]
      exact Finset.sum_congr rfl fun z hz => by simp [hz]
    rw [hsum, ← Nat.cast_smul_eq_nsmul ℚ]
    exact smul_ne_zero (Nat.cast_ne_zero.2 hne.card_pos.ne') hm

/-- **A half-turn-invariant summand has closure total twice its base total.** -/
theorem sum_halfTurnClosure_eq_two_smul (hab : Nat.Coprime a b) (ha : 1 < a) (hN : 0 < N)
    {f : Heights a b N → M} (hf : ∀ z ∈ halfTurnClosure a b N α, f (halfTurn z) = f z) :
    ∑ z ∈ halfTurnClosure a b N α, f z = (2 : ℚ) • ∑ z ∈ aboveReturnPaths a b N α, f z := by
  rw [sum_halfTurnClosure hab ha hN,
    Finset.sum_congr rfl fun z hz => hf z (aboveReturnPaths_subset_halfTurnClosure hz),
    two_smul]

/-- **The invariant shape is a restatement, not a weakening.** For a half-turn-invariant summand the
identity on the closure and the identity on the base paths are the same statement: `HJO.Sweep.Total`
is a `ℚ`-module, so there is no `2`-torsion to exploit. -/
theorem sum_halfTurnClosure_eq_zero_iff (hab : Nat.Coprime a b) (ha : 1 < a) (hN : 0 < N)
    {f : Heights a b N → M} (hf : ∀ z ∈ halfTurnClosure a b N α, f (halfTurn z) = f z) :
    ∑ z ∈ halfTurnClosure a b N α, f z = 0 ↔ ∑ z ∈ aboveReturnPaths a b N α, f z = 0 := by
  rw [sum_halfTurnClosure_eq_two_smul hab ha hN hf, smul_eq_zero]
  simp

end Obstruction

/-- **The only non-circular half-turn route implies the per-path clause.** A pairing across the
closure turns the base total into minus the mirror total, so it gives the obligation exactly when
the mirror total is known to vanish; and if the mirror half vanishes *pointwise* — the one way to
know it without assuming the obligation — then the summand vanishes at every base path.

Note the hypotheses: no coprimality, no positivity, no disjointness. The implication is the
transversal at its bluntest, one point at a time. -/
theorem eq_zero_of_halfTurn_pairing_of_mirror_eq_zero {M : Type*} [AddGroup M]
    {f : Heights a b N → M} (hpair : ∀ z ∈ halfTurnClosure a b N α, f z + f (halfTurn z) = 0)
    (hmirror : ∀ y ∈ belowReturnPaths a b N α.reverse, f y = 0) :
    ∀ z ∈ aboveReturnPaths a b N α, f z = 0 := by
  intro z hz
  have h1 := hpair z (aboveReturnPaths_subset_halfTurnClosure hz)
  rw [hmirror _ (halfTurn_mem_belowReturnPaths hz), add_zero] at h1
  exact h1

/-- **A summand vanishing on the mirror half makes the enlargement vacuous**: the closure total is
the base total, so nothing has been gained by enlarging the index set. -/
theorem sum_halfTurnClosure_eq_sum_aboveReturnPaths {M : Type*} [AddCommMonoid M]
    (hab : Nat.Coprime a b) (ha : 1 < a) (hN : 0 < N) {f : Heights a b N → M}
    (hmirror : ∀ y ∈ belowReturnPaths a b N α.reverse, f y = 0) :
    ∑ z ∈ halfTurnClosure a b N α, f z = ∑ z ∈ aboveReturnPaths a b N α, f z := by
  rw [sum_halfTurnClosure hab ha hN,
    Finset.sum_congr rfl fun z hz => hmirror _ (halfTurn_mem_belowReturnPaths hz),
    Finset.sum_const_zero, add_zero]

/-! ### The same three verdicts at the actual discrepancy -/

section Disc

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {A : ℕ}

/-- **Term by term on the closure is strictly stronger than term by term on the base paths**, since
the base paths are a subset. The conclusion is the per-path clause at this `α` and `A` — the
hypothesis of `HJO.Mellit.sweepAppend_of_forall_path` with the subtraction carried out as in
`HJO.Mellit.appendDisc` — and `HJO/Shuffle/SweepAppendBandPerPath.lean` records, by
computation, that it is false at `(a,b) = (2,3)`, `α = [1]`, `A = 1`. So the term-by-term reading on
the half-turn closure is false a fortiori, and this is the lemma that says so. -/
theorem forall_appendDisc_eq_zero_of_forall_halfTurnClosure
    (h : ∀ z ∈ halfTurnClosure a b α.sum α, appendDisc q u a b α A z = 0) :
    ∀ z ∈ aboveReturnPaths a b α.sum α, appendDisc q u a b α A z = 0 :=
  fun z hz => h z (aboveReturnPaths_subset_halfTurnClosure hz)

/-- **A half-turn pairing of the discrepancies, together with a vanishing mirror half, forces the
refuted per-path clause.** `HJO.Mellit.eq_zero_of_halfTurn_pairing_of_mirror_eq_zero` at
`HJO.Mellit.appendDisc`: the conclusion is again the per-path clause of
`HJO.Mellit.sweepAppend_of_forall_path`, which the computation refutes. Since the pairing alone is
information-free
(`HJO.Mellit.exists_halfTurn_pairing_sum_ne_zero`) and the invariant form is a restatement
(`HJO.Mellit.sum_halfTurnClosure_eq_zero_iff`), this exhausts the half-turn-closed shape. -/
theorem appendDisc_eq_zero_of_halfTurn_pairing_of_mirror_eq_zero
    (hpair : ∀ z ∈ halfTurnClosure a b α.sum α,
      appendDisc q u a b α A z + appendDisc q u a b α A (halfTurn z) = 0)
    (hmirror : ∀ y ∈ belowReturnPaths a b α.sum α.reverse, appendDisc q u a b α A y = 0) :
    ∀ z ∈ aboveReturnPaths a b α.sum α, appendDisc q u a b α A z = 0 :=
  eq_zero_of_halfTurn_pairing_of_mirror_eq_zero hpair hmirror

/-- **The sum of the discrepancies over the closure, split.** The obligation is the vanishing of the
first summand; the second is the mirror total, indexed by the base paths themselves. Any pointwise
relation between the discrepancy at `z` and at `halfTurn z` relates these two and nothing else. -/
theorem sum_halfTurnClosure_appendDisc (hab : Nat.Coprime a b) (ha : 1 < a) (hN : 0 < α.sum) :
    ∑ z ∈ halfTurnClosure a b α.sum α, appendDisc q u a b α A z
      = ∑ z ∈ aboveReturnPaths a b α.sum α, appendDisc q u a b α A z
        + ∑ z ∈ aboveReturnPaths a b α.sum α, appendDisc q u a b α A (halfTurn z) :=
  sum_halfTurnClosure hab ha hN _

end Disc

end HJO.Mellit

end
