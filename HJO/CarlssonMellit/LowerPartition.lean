/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.LowerPieces
public import HJO.CarlssonMellit.LowerTuples
public import HJO.CarlssonMellit.Runs
public meta import HJO.Attr

/-! # Freeing the last special label partitions the labellings

Two lemmas about the pieces `μ_r(π)` of the lowered characteristic series and the index
sets they sum over.

The first, `HJO.Dyck.lowerCharPiece_zero`, is the identification of the zeroth piece: the lower
tuple at `r = 0` is the identity tuple, so `μ_0(π) = ν_{Id_k}(π)` with no computation at all.

The second, that `U(π, Id_{k-1})` is the disjoint union of the sets `U(π, σ^{[r]})`, is the
combinatorial heart of the lowering recursion. Deleting the last entry of the prescription leaves
the set `U(π, Id_{k-1})` of labellings whose first `k - 1` letters are `0, …, m - 1` in order and
which separate the attacking pairs of `π`, the letter at the `k`-th position being otherwise
unprescribed. It is not unconstrained, though: on a partial Dyck path of level `k = m + 1` every
earlier position attacks the position `m`, all the rows below the level being full above the
diagonal, so the letter there avoids each of `0, …, m - 1` and is `m + r` for exactly one `r ≥ 0`.
Sorting the labellings by that `r` — Carlsson and Mellit's `r = w_k - k` — cuts `U(π, Id_{k-1})`
into the sets `U(π, σ^{[r]})`, and the constancy of `w_k` on a piece is what lets the variable
`z^{(k)}_{k+r}` come out of the sum.

## Main results

* `HJO.Dyck.lowerCharPiece_zero`: `μ_0(π) = ν_{Id_k}(π)`.
* `HJO.Dyck.IsPartialDyck.noAttackLabellings_identityTuple_eq_iUnion_lowerTuple`: the union half of
  the partition, that `U(π, Id_{k-1})` is the union of the sets `U(π, σ^{[r]})`.
* `HJO.Dyck.pairwise_disjoint_noAttackLabellings_lowerTuple`: the disjointness half of the
  partition, that those sets are pairwise disjoint.

Along the way, `HJO.Dyck.noAttackLabellings_lowerTuple_eq_sep` describes each piece as a fibre:
`U(π, σ^{[r]}) = {w ∈ U(π, Id_{k-1}) | w_k = k + r}`, for an arbitrary sequence and with no
condition on it whatever.

## Implementation notes

The level is written `m + 1`, so the condition `k ≥ 1` is carried by the shape of the type as in
`HJO.Dyck.lowerTuple`, and `Id_{k-1}` is `HJO.Dyck.identityTuple m`, a tuple on `Fin m`, while each
`σ^{[r]}` is a tuple on `Fin (m + 1)`. Positions and letters are indexed from `0`, as for
`HJO.Dyck.noAttackLabellings`, so Carlsson and Mellit's freed letter `k + r` is `m + r` and their
`k`-th position is the position `m`. That position is named as a `p : Fin N` together with
`(p : ℕ) = m` rather than as `Fin.mk`, so that a consumer holding the position in any spelling can
use these lemmas without a proof-term coincidence.

*The two halves of "disjoint union" are two declarations*, which together state the partition: the
equation splits the index set of a sum and the disjointness makes that split a sum of sums, so the
consumers differ. Nothing bundled fits — `Setoid.IsPartition` and `IndexedPartition` partition an
ambient type rather than a subset of `Fin N → ℕ`, and `Finpartition` has finitely many parts where
this family is indexed by `ℕ`. A consumer wanting the sentence as one term has
`Set.unionEqSigmaOfDisjoint`, which takes the disjointness verbatim, `Function.onFun` and all, and
returns `↑(⋃ r, t r) ≃ Σ r, ↑(t r)`.

*Hypotheses dropped.* For `HJO.Dyck.lowerCharPiece_zero` both natural side conditions go:
`N ≥ k` and `π ∈ 𝔻_{k,N}` are never read, the two sums being the same sum of the same summands once
`HJO.Dyck.lowerTuple_zero` has rewritten the prescription, and neither
`HJO.Dyck.lowerCharPiece` nor `HJO.Dyck.partialCharSeries` imposes a condition on the sequence. For
the disjointness half, `HJO.Dyck.pairwise_disjoint_noAttackLabellings_lowerTuple`, the path
hypothesis goes and only the existence of the position survives: two distinct fibres of `w ↦ w_m`
are disjoint whatever the sequence, and `m < N` is genuinely needed — at `N = 1` and `m = 1` the
position does not exist, the last entry of `σ^{[r]}` prescribes nothing, every `U(0, σ^{[r]})` is
`{w | w_0 = 0}`, and `![0]` lies in all of them at once.

*What the union half spends the hypothesis on.* `HJO.Dyck.IsPartialDyck.le_length` supplies the
position `m`, and `HJO.Dyck.IsPartialDyck.eq_zero_of_lt_level` at the row `m` supplies the cells
`(i, m)` of `At(π)` for `i < m`, through `HJO.Dyck.mem_attackSet_level_of_lt`,
which is where the letters `0, …, m - 1` are barred from the position
`m`. This is the only place the attack set is read and the only mathematical content of the lemma;
one level down the equation is false, at `Fin.val : Fin 3 → ℕ`, a partial Dyck path of level `1`
whose entry at the row `1` is `1` and not `0`, whose attack set is empty, and for which `![0, 0, 0]`
lies in `U(π, Id_1)` and in no `U(π, σ^{[r]})`, the latter asking `w_1 = 1 + r ≥ 1`. The hypothesis
`HJO.Dyck.IsPartialDyck` is kept rather than replaced by those two facts because every consumer
holds it — `HJO.Dyck.insertFront_partialCharSeries_identityTuple` applies the lemma to a path of
`𝔻_{k,N}`.

Two hypotheses that Carlsson and Mellit's definitions need are absent because
`HJO.Dyck.noAttackLabellings` carries none: `HJO.Dyck.IsPartialDyck.of_le_level`, putting `π` in
`𝔻_{k-1,N}` so that `U(π, Id_{k-1})` is "defined", and `HJO.Dyck.lowerTuple_injective`, making the
entries of `σ^{[r]}` distinct so that each `U(π, σ^{[r]})` is. Both remain the reason the sets are
the ones Carlsson and Mellit define, and neither is a side condition in Lean.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 4, the line `χ'_{k,r}(π) = χ'_σ(π), σ = (1, 2, …, k-1, k+r)` and the sentence "to
get to the second equality we have summed over all possible values of `r = w_k - k` that do not
result in an attack".
-/

@[expose] public section

namespace HJO.Dyck

/-! ### The zeroth piece -/

variable {K : Type*} [CommRing K] {N m : ℕ}

/-- **The zeroth piece is the characteristic series at the identity tuple.**
`μ_0(π) = ν_{Id_k}(π)`, for the level `k = m + 1`. The lower tuple at `r = 0` is the identity tuple
by `HJO.Dyck.lowerTuple_zero`, so the two sums of `HJO.Dyck.lowerCharPiece` and
`HJO.Dyck.partialCharSeries` are the same sum of the same summands.

The side conditions `N ≥ k` and `π ∈ 𝔻_{k,N}` are not needed and are not assumed:
neither series imposes a condition on the sequence, and the identity is one rewriting of the
prescription. -/
@[hjo "lem_cm_mu_zero"]
theorem lowerCharPiece_zero (q : K) (m : ℕ) {N : ℕ} (x : Fin N → ℕ) :
    lowerCharPiece q m x 0 = partialCharSeries q (m + 1) x (identityTuple (m + 1)) := by
  rw [lowerCharPiece_eq_partialCharSeries, lowerTuple_zero]

/-! ### The pieces are the fibres of the freed letter -/

variable {x w : Fin N → ℕ} {r : ℕ}

/-- **Each piece is a fibre of the freed letter.** For a position `p` of index `m`, the labellings
prescribed by `σ^{[r]}` are exactly those prescribed by `Id_{k-1}` that carry the letter `m + r` at
`p`: `U(π, σ^{[r]}) = {w ∈ U(π, Id_{k-1}) | w_k = k + r}`. The first `m` entries of the two tuples
agree by `HJO.Dyck.lowerTuple_castSucc`, and the last entry of `σ^{[r]}` is the freed letter by
`HJO.Dyck.lowerTuple_last`, so the only difference between the two prescriptions is the letter at
`p`.

No condition is imposed on the sequence: this is a statement about the two prescriptions alone, and
it is what pins the index `r` of the piece a labelling belongs to, Carlsson and Mellit's
`r = w_k - k`. -/
theorem noAttackLabellings_lowerTuple_eq_sep (x : Fin N → ℕ) (r : ℕ) {p : Fin N}
    (hp : (p : ℕ) = m) :
    noAttackLabellings x (lowerTuple m r) =
      {w ∈ noAttackLabellings x (identityTuple m) | w p = m + r} := by
  ext w
  refine ⟨fun hw => ⟨⟨fun i j hij => ?_, hw.2⟩, ?_⟩, fun hw => ⟨fun i j => ?_, hw.1.2⟩⟩
  · rw [eq_of_mem_noAttackLabellings hw (j := j.castSucc) (by simpa using hij),
      lowerTuple_castSucc]
  · rw [eq_of_mem_noAttackLabellings hw (j := Fin.last m) (by simpa using hp),
      lowerTuple_last]
  · induction j using Fin.lastCases with
    | last =>
      intro hij
      have hi : i = p := Fin.ext (by rw [hp]; simpa using hij)
      rw [lowerTuple_last, hi]
      exact hw.2
    | cast j =>
      intro hij
      rw [lowerTuple_castSucc]
      exact eq_of_mem_noAttackLabellings hw.1 (by simpa using hij)

/-- The letter a labelling prescribed by `σ^{[r]}` carries at the position of index `m` is the freed
letter `m + r`, Carlsson and Mellit's `w_k = k + r`: the last entry of the prescription, read off
`HJO.Dyck.noAttackLabellings_lowerTuple_eq_sep`. -/
theorem apply_eq_of_mem_noAttackLabellings_lowerTuple
    (hw : w ∈ noAttackLabellings x (lowerTuple m r)) {p : Fin N} (hp : (p : ℕ) = m) :
    w p = m + r := by
  rw [noAttackLabellings_lowerTuple_eq_sep x r hp] at hw
  exact hw.2

/-! ### The partition -/

/-- **The disjointness half of `HJO.Dyck.pairwise_disjoint_noAttackLabellings_lowerTuple`.** The
sets `U(π, σ^{[r]})` are pairwise disjoint: a labelling of the `r`-th one carries the letter `m + r`
at the position of index `m`, and distinct `r` give distinct letters there.

The `π ∈ 𝔻_{k,N}` is not needed for this half and is not assumed — two distinct fibres
of the map sending a labelling to its letter at that position are disjoint whatever the sequence.
The `N ≥ k`, here `m < N`, is needed: without the position the last entry of `σ^{[r]}`
prescribes nothing and the sets coincide. -/
@[hjo "lem_cm_lower_partition"]
theorem pairwise_disjoint_noAttackLabellings_lowerTuple (x : Fin N → ℕ) (hm : m < N) :
    Pairwise (Function.onFun Disjoint fun r : ℕ => noAttackLabellings x (lowerTuple m r)) := by
  intro r r' hrr'
  rw [Function.onFun, Set.disjoint_left]
  intro w hw hw'
  have h := apply_eq_of_mem_noAttackLabellings_lowerTuple hw (p := ⟨m, hm⟩) rfl
  have h' := apply_eq_of_mem_noAttackLabellings_lowerTuple hw' (p := ⟨m, hm⟩) rfl
  omega

/-- **Every earlier letter is barred from the freed position.** On a partial Dyck path of level
`k = m + 1`, a labelling of `U(π, Id_{k-1})` carries at the position `p` of index `m` a letter at
least `m`: were it some `i < m`, the position of index `i` would carry the letter `i` too, and
`(i, m) ∈ At(π)` by `HJO.Dyck.mem_attackSet_level_of_lt` forbids the repetition.

This is the whole mathematical content of
`HJO.Dyck.pairwise_disjoint_noAttackLabellings_lowerTuple`, and the only place its hypothesis is
read. -/
theorem IsPartialDyck.le_apply_of_mem_noAttackLabellings_identityTuple
    (h : IsPartialDyck (m + 1) N x) (hw : w ∈ noAttackLabellings x (identityTuple m)) {p : Fin N}
    (hp : (p : ℕ) = m) : m ≤ w p := by
  by_contra hlt
  rw [Nat.not_le] at hlt
  have hmN : m < N := by rw [← hp]; exact p.isLt
  refine ne_of_mem_noAttackLabellings hw (i := ⟨w p, hlt.trans hmN⟩) (j := p)
    (by rw [hp]; exact mem_attackSet_level_of_lt h hlt) ?_
  exact eq_of_mem_noAttackLabellings hw (j := ⟨w p, hlt⟩) rfl

/-- **The union half of `HJO.Dyck.pairwise_disjoint_noAttackLabellings_lowerTuple`.** For a partial
Dyck path `π` of level `k = m + 1` and length `N`, the set `U(π, Id_{k-1})` of labellings with the
first `k - 1` letters prescribed is the union over `r ≥ 0` of the sets `U(π, σ^{[r]})` of labellings
whose `k`-th letter is the freed label `m + r`.

Each piece is contained in the union's left-hand side because the two prescriptions agree below the
position `m`. Conversely the letter there is at least `m`, every earlier position attacking it on a
partial Dyck path, so it is `m + r` for the `r` of
`HJO.Dyck.IsPartialDyck.le_apply_of_mem_noAttackLabellings_identityTuple`; that `r` is Carlsson and
Mellit's `w_k - k`. -/
@[hjo "lem_cm_lower_partition"]
theorem IsPartialDyck.noAttackLabellings_identityTuple_eq_iUnion_lowerTuple
    (h : IsPartialDyck (m + 1) N x) :
    noAttackLabellings x (identityTuple m) = ⋃ r : ℕ, noAttackLabellings x (lowerTuple m r) := by
  have hm : m < N := h.le_length
  have hp : ((⟨m, hm⟩ : Fin N) : ℕ) = m := rfl
  refine Set.eq_of_subset_of_subset (fun w hw => Set.mem_iUnion.2 ⟨w ⟨m, hm⟩ - m, ?_⟩)
    (Set.iUnion_subset fun r w hw => ?_)
  · have hle := h.le_apply_of_mem_noAttackLabellings_identityTuple hw hp
    rw [noAttackLabellings_lowerTuple_eq_sep x _ hp]
    exact ⟨hw, by omega⟩
  · rw [noAttackLabellings_lowerTuple_eq_sep x r hp] at hw
    exact hw.1

end HJO.Dyck
