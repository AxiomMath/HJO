/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.PartialPaths
public meta import HJO.Attr

/-! # The step word of a Dyck path read at level zero

A partial Dyck path of level `k` and length `N` is read by `HJO.Dyck.partialStepWord` as a word
`w_k(π) = ε₁ ⋯ ε_{2N-k}` in two letters, and a Dyck path of length `N` is read by
`HJO.Dyck.stepWord` as a word `w(π) = ε₁ ⋯ ε_{2N}`: once the entries below the level vanish, the
first is the second with the `k` prepended north steps deleted and every later marking position
shifted down by `k`. At `k = 0` nothing is deleted and nothing is shifted, so the two prescriptions
coincide letter for letter — both mark the position `s` with a north step exactly when
`s = x_j + j - 1` for some `1 ≤ j ≤ N` — and the two words are equal.

This is the step the character recursion of the paper's Section 4 takes at its top. Theorem 4.4
reads a Dyck path through `w(π)`, while the induction that proves it consumes the level-indexed
`w_k(π)`, prepending one step at a time and moving the level with it; the two readings have to be
identified once, at the level where the recursion ends, and that identification is this lemma.

## Main results

* `HJO.Dyck.partialStepWord_zero_left`: `w_0(π) = w(π)`.

## Implementation notes

The lemma is usually stated for a Dyck path `π` of length `n ≥ 1`; the statement here carries
neither hypothesis, because neither is used. Its proof observes only that the path lies in
`𝔻_{0,n}`, there being no condition on its entries, and that at `k = 0` the two prescriptions read
the same: the level-`k` reading contributes the range restriction `0 ≤ j`, which is vacuous, and the
shift `+ 0` on the marking position, and its length `2N - 0` is `2N`, so the letters agree one by
one for an arbitrary `x : Fin N → ℕ`. Neither monotonicity of the entries, nor the diagonal bound
`x_j ≤ j`, nor `n ≥ 1` enters, and at `N = 0` both sides are the empty word, so the hypothesis
`n ≥ 1` excludes no case rather than guarding one.

The equation is the level-`0` case of `HJO.Dyck.partialStepWord_eq_drop_stepWord`, whose hypothesis
`∀ l, (l : ℕ) < 0 → x l = 0` is vacuous, followed by `List.drop_zero`. It is a declaration of its
own, and `@[simp]`, for the reason that makes a specialisation worth a name: the general lemma
rewrites to `(stepWord x).drop 0`, which is not yet `stepWord x` and which carries a hypothesis that
has to be discharged before the rewrite fires, so `partialStepWord 0 x` is reduced to the more
primitive word — the one with the larger API, the letter counts and the first and last letters of
`HJO/CarlssonMellit/SquareDyck.lean` — by this lemma alone.

The level is not idle at a general `k`, so the specialisation is not vacuous: by
`HJO.Dyck.length_partialStepWord` and `HJO.Dyck.length_stepWord` the two words have `2N - k` and
`2N` letters, so at any `k ≥ 1` and `N ≥ 1` they already differ in length, and
`HJO.Dyck.partialStepWord_level_restriction_example` exhibits two entries at which the
delete-and-shift reading itself fails without the hypothesis that the entries below the level
vanish.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, arXiv:1508.06239v3, J. Amer. Math.
Soc. **31** (2018) 661--697: Theorem 4.4, which reads a Dyck path of length `n` as the word
`ε₁ ⋯ ε_{2n}` of plus and minus symbols "reading `π` from bottom left to top right", that is at
level `0`; the partial paths `𝔻_{k,n}`; and the level-indexed recursion `χ_{k+1}(Eπ) = d₊ χ_k(π)`,
`χ_{k-1}(Nπ) = d₋ χ_k(π)`, above which the paper makes the same identification at the level of the
characteristic functions, "for `k = 0` we recover `χ(π)`". The lemma here is
`HJO.Dyck.partialStepWord_zero_left`, using `HJO.Dyck.IsSquareDyck`, `HJO.Dyck.stepWord` and
`HJO.Dyck.partialStepWord`; consumed by the proof of
`HJO.Dyck.realisation_constantCoeff_markedWordOp'`.
-/

@[expose] public section

namespace HJO.Dyck

/-- **At level zero the two readings of a Dyck path agree**: `w_0(π) = w(π)`. The level-`k` word is
the full word with the `k` prepended north steps deleted and every later marking position shifted
down by `k`, and at `k = 0` there is nothing to delete and nothing to shift, so the words are equal
letter for letter.

Stated for an arbitrary sequence of entries, the hypotheses that `π` be a Dyck path and
that its length be positive being unused: the agreement is between the two prescriptions and not a
property of a path. -/
@[simp, hjo "lem_cm_partial_word_zero"]
theorem partialStepWord_zero_left {N : ℕ} (x : Fin N → ℕ) :
    partialStepWord 0 x = stepWord x :=
  (partialStepWord_eq_drop_stepWord (by simp)).trans List.drop_zero

end HJO.Dyck
