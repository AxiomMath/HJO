/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.Tuples
public meta import HJO.Attr

/-! # The tuples of the lowering recursion are tuples of distinct labels

The lowering recursion of Carlsson and Mellit prescribes the first `k` letters of the labellings it
counts by the tuple `σ^{[r]} = (1, …, k-1, k+r)`, and the characteristic function `ν_σ(π)` is
indexed by tuples whose entries are *distinct*. This file discharges that side condition: the
entries of `σ^{[r]} = HJO.Dyck.lowerTuple m r` are pairwise distinct for every `r`.

## Main results

* `HJO.Dyck.lowerTuple_injective`: the entries of `σ^{[r]}` are pairwise distinct, for every level
  `k = m + 1 ≥ 1` and every `r ≥ 0`. The freed label `m + r` sits at the last position and is at
  least `m`, while every earlier position carries its own index, which is below `m`.

## Implementation notes

Positions and labels are both indexed from `0`, as in `HJO.Dyck.lowerTuple`, so Carlsson and
Mellit's label `i` is `i - 1` here and its side condition `k ≥ 1` is carried by the shape
`Fin (m + 1)` of the index type.

"Pairwise distinct entries" is `Function.Injective` on the tuple, which is the idiom of
`HJO.Dyck.identityTuple_injective` and `HJO.Dyck.cycleTuple_injective` for the two sibling
families; the `r ≥ 0` is vacuous on `ℕ`, and no bound relating `m + r` to a level is
needed, the distinctness coming from `m + r ≥ m` alone.

The companion fact `σ^{[0]} = Id_k` is `HJO.Dyck.lowerTuple_zero` in
`HJO/CarlssonMellit/Tuples.lean` next to the definition, where it is a `simp` lemma. It is not
restated here: the two declarations together describe the lower tuples, and duplicating the `r = 0`
computation in this file would add a second name for one fact.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 4, the lowering recursion: Lemma `HJO.Dyck.lowerTuple_injective` and definitions
`HJO.Dyck.lowerTuple`, `HJO.Dyck.identityTuple`.
-/

@[expose] public section

namespace HJO.Dyck

/-- **The freeing tuples have distinct entries.** The entries of
`σ^{[r]} = (1, …, k-1, k+r)` are pairwise distinct, for every level `k = m + 1 ≥ 1` and every
`r ≥ 0`, which is what makes it a tuple of labels and so an admissible index of the characteristic
function `ν_σ`. The two earlier entries of a pair are their own positions, hence distinct; the last
entry is the freed label `m + r ≥ m`, which no earlier position carries.

The lemma's second conclusion, `σ^{[0]} = Id_k`, is `HJO.Dyck.lowerTuple_zero`. -/
@[hjo "lem_cm_lower_tuple_distinct"]
theorem lowerTuple_injective (m r : ℕ) : Function.Injective (lowerTuple m r) := by
  intro a b hab
  revert hab
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => exact fun _ => rfl
    | cast j =>
      refine fun hab => absurd hab ?_
      rw [lowerTuple_last, lowerTuple_castSucc]
      have := j.isLt
      omega
  | cast i =>
    induction b using Fin.lastCases with
    | last =>
      refine fun hab => absurd hab ?_
      rw [lowerTuple_castSucc, lowerTuple_last]
      have := i.isLt
      omega
    | cast j =>
      refine fun hab => congrArg Fin.castSucc (Fin.ext ?_)
      rw [lowerTuple_castSucc, lowerTuple_castSucc] at hab
      exact hab

end HJO.Dyck
