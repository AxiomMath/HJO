/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.PartialPaths
public import HJO.CarlssonMellit.Tuples
public meta import HJO.Attr

/-! # One step of the step word of a partial Dyck path

The character recursion of the paper's Section 4 consumes a partial Dyck path through its step word
`w_k(π) = ε₁ ⋯ ε_{2N-k}` and strips one letter at a time, raising or lowering the level according to
whether that letter marks an east or a north step. This file takes that step, in its two halves.

North: if `π` read at level `k` has a next entry and that entry is minimal — in one-based terms
`k < N` and `x_{k+1} = 1` — then the level-`k` word is the level-`(k+1)` word of the *same* sequence
with one north step prepended, `w_k(π) = - · w_{k+1}(π)`.

East: if `π` read at level `k + 1` has no minimal entry from the level on — in one-based terms
`k = N` or `x_{k+1} ≥ 2` — then the first step of `π` is east, that step is deleted by `D_k`, the
level and the length both drop by one, and `w_{k+1}(π) = + · w_k(D_k(π))`.

Which of the two applies is the dichotomy
`HJO.Dyck.IsSquareDyck.xor_exists_apply_eq_zero_level_pos`, whose two alternatives are verbatim the
hypotheses here, the north one at the level `k` and the east one at the level `k + 1` with its
`0 < k + 1` structural in this spelling.

## Main results

* `HJO.Dyck.partialStepWord_eq_U_cons_partialStepWord_succ`: the clauses `ε₁ = -`
  and `ε_s = η_{s-1}`, as the single equation `w_k(π) = - · w_{k+1}(π)` of words.
* `HJO.Dyck.partialStepWord_succ_eq_D_cons_partialStepWord_eastInverse`: the clauses
  `ε₁ = +` and `ε_s = η_{s-1}`, as the single equation `w_{k+1}(π) = + · w_k(D_k(π))` of words.

## Implementation notes

Levels and lengths are unshifted while positions and entries are indexed from `0`, as in
`HJO.Dyck.IsPartialDyck` and `HJO.Dyck.partialStepWord`: the one-based entry `x_j` is
`x ⟨j - 1, _⟩ + 1`, so its `x_j = 1` reads `x ⟨k, hk⟩ = 0` and its `x_j ≥ 2` reads `0 < x ⟨j-1, _⟩`,
while its letters `-` and `+` are `DyckStep.U` and `DyckStep.D`. In the east half the statement's
level is `k + 1` and its length `n + 1`, the spelling of the sibling
`HJO.Dyck.isPartialDyck_eastInverse`, so that the level and the length of `D_k(π)` are `k` and `n`
with no truncated subtraction and the level bound `k ≥ 1` is structural rather than a hypothesis;
`D_k` is `HJO.Dyck.eastInverse (k + 1)`, whose entries are the one-based `x'_j = x_{j+1} - 1`.

The statement has two clauses in each half, `ε₁ = ∓` and `ε_s = η_{s-1}` for `2 ≤ s ≤ 2N-k`.
They are one equation of lists: the two words have lengths `2N-k` and `2N-k-1` by
`HJO.Dyck.length_partialStepWord`, so a head together with a positionwise agreement of the tails
over the whole range is exactly a `List.cons` equation. The departure is of form alone and is not a
strengthening: the clauses in one-based indices follow from the equation,
the first with no hypothesis and the second with the lower bound `2 ≤ s` alone, by
`List.getElem?_cons_succ`, and they return it by `List.ext_getElem?` with no hypothesis whatever,
the two words being `none` together past their lengths. What the `cons` form buys is spent at the
call site: the recursion composes one operator per letter, so it wants the word *as* a letter
followed by a word, and from this equation its step is `List.foldr_cons`. The upper bound
`s ≤ 2N-k` goes with it; the lower bound is not decoration but the content of the clause, the two
truncated subtractions collapsing together at `s ≤ 1`.

In the north half both hypotheses are recovered from the conclusion, so the two together are
equivalent to it: the head reading `HJO.Dyck.getElem_partialStepWord_eq_U_iff` at `s = 0` forces the
marking index to be `k` itself, concluding `k < N` and the minimality of the entry. The ambient
hypotheses `π ∈ 𝔻_{k,N}` and `N ≥ k` are therefore absent, and they could not replace `hx` in any
case: membership gives `x l = 0` for `l < k` alone, and the conclusion fails at `k = 1` on the
path `(1, 2, 2) ∈ 𝔻_{1,3}`, formalised as `HJO.Dyck.isPartialDyck_example_one_three`, whose word
`HJO.Dyck.partialStepWord_example_one_three` begins with an east step.

In the east half the hypothesis is the positivity of every entry from the level on, `0 < x j` for
`k + 1 ≤ j`, and not its instance at the level together with monotonicity. It is what both clauses
spend and what makes them true: an entry `x j = 0` with `k + 1 ≤ j` marks a north step of `D_k(π)`
at the position `j - 1 - k` while `x_j - 1` truncates instead of shifting, so the letters part
company there — `![0, 0] ∈ 𝔻_{1,2}` has a north step first, and there the equation fails,
`w_1 = [U, D, D]` against `+ · w_0(D_1) = [D, U, D]`. The hypothesis in the form `π ∈ 𝔻_{k+1,n+1}`
with `k = N` or `x_{k+1} ≥ 2` follows, and the derivation spends only two of its data: given
`Monotone x` and `k + 1 ≤ n + 1`, the disjunction `k + 1 = n + 1 ∨ 0 < x ⟨k+1, _⟩` gives the
hypothesis, the first branch by `j ≤ n < k + 1` and the second by monotonicity — so of
`π ∈ 𝔻_{k+1,n+1}` only `HJO.Dyck.IsSquareDyck.mono` and `le_length` are read, the diagonal bound and
the vanishing of the entries below the level being dead, and the separate hypothesis `N ≥ k` being
`le_length`.

The bound `hk : k ≤ n` of the east half is the hypothesis `N ≥ k` and is read for the lengths alone,
`2(n+1)-(k+1) = (2n-k)+1`, for which the sharp condition is `k ≤ 2n`. The bound `k ≤ n` is kept
because the added region `n < k ≤ 2n` holds none of the objects of the recursion and none of this
content: no sequence lies in `𝔻_{k+1,n+1}` there, and both words are free of north letters, every
marking index `j` being at most `n < k + 1`. It is also the hypothesis of
`HJO.Dyck.isPartialDyck_eastInverse`, the sibling that makes the right-hand word the word of a
partial Dyck path of level `k`, so one `hk` serves the recursion's whole east step.

Neither half assumes the path, `HJO.Dyck.partialStepWord` and `HJO.Dyck.eastInverse` being total, so
all four words are written down without membership. The shift is by one level in each half and is
not stated for `m` levels at once: the recursion strips one letter per step, so an `m`-fold form has
no call site.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, arXiv:1508.06239v3,
J. Amer. Math. Soc. **31** (2018) 661--697, Section 4: the recursion
`χ_{k+1}(Eπ) = d₊ χ_k(π)` and `χ_{k-1}(Nπ) = d₋ χ_k(π)` for `π ∈ 𝔻_k`, read in the
direction the word is consumed, with `E` and `N` adding an east and a north step to the beginning of
the path; and Theorem 4.4 for the alphabet and the
reading order. The paper's two operators differ in their effect on the length, which is what shapes
the two halves differently: `π ∈ 𝔻_{k,n}` gives `Nπ ∈ 𝔻_{k-1,n}`, the same `n`, so the
north half moves the level and keeps the sequence, while `Eπ ∈ 𝔻_{k+1,n+1}` raises both
and the east half shortens the path to `D_k(π)`. The displayed clauses `ε₁ = ∓` and `ε_s = η_{s-1}`
are the transcription of that recursion into coarea coordinates, not a formula the
paper displays.
-/

@[expose] public section

namespace HJO.Dyck

open DyckStep

/-! ### The word when the first step is north -/

/-- When the next step of a partial Dyck path of level `k` is north — in one-based terms
`x_{k+1} = 1`, here `x ⟨k, hk⟩ = 0` — its step word at level `k` is its step word at level `k + 1`
with one north step prepended: the clauses `ε₁ = -` together with `ε_s = η_{s-1}` for
`2 ≤ s ≤ 2N-k`, as a single equation of words. This is the north half of the step the character
recursion takes, the letter stripped being the prepended `U`. -/
@[hjo "lem_cm_word_north"]
theorem partialStepWord_eq_U_cons_partialStepWord_succ {k N : ℕ} {x : Fin N → ℕ} (hk : k < N)
    (hx : x ⟨k, hk⟩ = 0) :
    partialStepWord k x = U :: partialStepWord (k + 1) x := by
  refine List.ext_getElem (by simp only [length_partialStepWord, List.length_cons]; omega)
    fun s h₁ h₂ => ?_
  rcases s with _ | s
  · rw [List.getElem_cons_zero, getElem_partialStepWord_eq_U_iff k x 0 h₁]
    exact ⟨⟨k, hk⟩, le_rfl, by simp [hx]⟩
  · have h₃ : s < (partialStepWord (k + 1) x).length := by simpa using h₂
    rw [List.getElem_cons_succ, getElem_partialStepWord k x (s + 1) h₁,
      getElem_partialStepWord (k + 1) x s h₃]
    refine if_congr ⟨fun ⟨j, hj, hj'⟩ => ⟨j, ?_, by omega⟩,
      fun ⟨j, hj, hj'⟩ => ⟨j, by omega, by omega⟩⟩ rfl rfl
    rcases eq_or_lt_of_le hj with heq | hlt
    · have hxj : x j = 0 := by
        rw [Fin.val_injective (show ((⟨k, hk⟩ : Fin N) : ℕ) = (j : ℕ) from heq)] at hx
        exact hx
      omega
    · omega

/-! ### The word when the first step is east -/

/-- When the next step of a partial Dyck path of level `k + 1` is east — in one-based terms `k = N`
or `x_{k+1} ≥ 2`, here the positivity `0 < x j` of every entry from the level on, which monotonicity
makes equivalent to its instance at the level — its step word at level `k + 1` is the step word at
level `k` of `D_k(π) = eastInverse (k + 1) x` with one east step prepended: the clauses `ε₁ = +`
together with `ε_s = η_{s-1}` for `2 ≤ s ≤ 2N-k`, as a single equation of words. This is the east
half of the step the character recursion takes, the letter stripped being the prepended `D`. -/
@[hjo "lem_cm_word_east"]
theorem partialStepWord_succ_eq_D_cons_partialStepWord_eastInverse {k n : ℕ}
    {x : Fin (n + 1) → ℕ} (hk : k ≤ n) (hx : ∀ j : Fin (n + 1), k + 1 ≤ (j : ℕ) → 0 < x j) :
    partialStepWord (k + 1) x = D :: partialStepWord k (eastInverse (k + 1) x) := by
  refine List.ext_getElem (by simp only [length_partialStepWord, List.length_cons]; omega)
    fun s h₁ h₂ => ?_
  rcases s with _ | s
  · rw [List.getElem_cons_zero, getElem_partialStepWord_eq_D_iff (k + 1) x 0 h₁]
    intro j hj
    have := hx j hj
    omega
  · have h₃ : s < (partialStepWord k (eastInverse (k + 1) x)).length := by simpa using h₂
    rw [List.getElem_cons_succ, getElem_partialStepWord (k + 1) x (s + 1) h₁,
      getElem_partialStepWord k (eastInverse (k + 1) x) s h₃]
    refine if_congr ⟨?_, ?_⟩ rfl rfl
    · rintro ⟨j, hj, hj'⟩
      have hjn : (j : ℕ) < n + 1 := j.isLt
      have hpos : 0 < x j := hx j hj
      obtain ⟨m, hm⟩ : ∃ m, (j : ℕ) = m + 1 := ⟨(j : ℕ) - 1, by omega⟩
      have hmn : m < n := by omega
      have hval : ((⟨m, hmn⟩ : Fin n) : ℕ) = m := rfl
      have hxeq : x (⟨m, hmn⟩ : Fin n).succ = x j :=
        congrArg x (Fin.val_injective (by simp [hm]))
      refine ⟨⟨m, hmn⟩, by omega, ?_⟩
      rw [eastInverse_of_le _ (show k + 1 ≤ ((⟨m, hmn⟩ : Fin n) : ℕ) + 1 by omega), hxeq]
      omega
    · rintro ⟨i, hi, hi'⟩
      have hik : k + 1 ≤ ((i : ℕ)) + 1 := by omega
      have hpos : 0 < x i.succ := hx i.succ (by simpa using hik)
      rw [eastInverse_of_le _ hik] at hi'
      exact ⟨i.succ, by simpa using hik, by simp only [Fin.val_succ]; omega⟩

end HJO.Dyck
