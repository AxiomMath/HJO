/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.EastAttack
public import HJO.CarlssonMellit.PartialPaths
public import HJO.CarlssonMellit.Tuples
public import HJO.DyckAttackSets
public import HJO.DyckInversions
public meta import HJO.Attr

/-! # Prepending an east step: the new path and its inversions

Carlsson and Mellit run their recursion on the partial Dyck paths `𝔻_{k,n}`, the paths from `(0, k)`
to `(n, n)` staying weakly above the diagonal, because — unlike the set `𝔻` of Dyck paths — the
union of the sets `𝔻_k` is closed under adding a north or an east step to the *beginning* of the
path. This file carries the east half of that closure and the effect of the same move on the
inversion statistic, the two facts the raising recursion `ν_{σ^{(k+1)}}(E_kπ) = q^kΦ_k(ν_{Id_k}(π))`
is assembled from.

The closure: the map `E_k` of `HJO.Dyck.prependEast`, which translates the path by `(1, 1)` and
prepends an east step from `(0, k+1)` to `(1, k+1)`, carries `𝔻_{k,n}` into `𝔻_{k+1,n+1}`. In the
coarea encoding of `HJO.Dyck.IsSquareDyck`, where a path of length `n` is its sequence of abscissas
`x_1 ≤ ⋯ ≤ x_n` with `x_j ≤ j` and a partial path of level `k` is one with `x_1 = ⋯ = x_k = 1`, the
four things to check are these: the new entries are weakly increasing, including across
the boundary of the two clauses of `E_k`, where `x'_{k+1} = 1` meets `x'_{k+2} = x_{k+1} + 1 ≥ 2`;
they satisfy `x'_j ≤ j`, since `x'_j = x_{j-1} + 1 ≤ (j-1) + 1`; the first `k + 1` of them are
minimal, which is the first clause of `E_k` outright; and `n + 1 ≥ k + 1`. The north half is
`HJO.Dyck.IsPartialDyck.of_le_level`.

The statistic: prepending an east step to `π` and the new special letter `k` to a labelling `w`
carrying the letter `i` at each position `i < k` — the prescription that the identity tuple `Id_k`
imposes on the no-attack labellings `U(π, Id_k)` — raises the inversion number by exactly `k`,

`inv(At(E_kπ), E^*_kw) = inv(At(π), w) + k`.

The inversion set is computed outright, as the disjoint union of the `k` pairs `(0, j + 1)` with
`j < k` and the translate by `(1, 1)` of the whole of `Inv(At(π), w)`. A cell of `At(E_kπ)` lies
either in the window `{(i, j) : i < j ≤ k}` of the new level, whose rows are full because they carry
the `k + 1` virtual north steps, or is the translate of a cell of `At(π)` in a row at or above the
level. On the window the prepended labelling reads `k, 0, 1, …, k - 1`: the first position carries
the largest of those letters and so inverts each of the `k` pairs `(0, j)`, while the pairs `(i, j)`
with `1 ≤ i < j ≤ k` carry `i - 1 < j - 1` and invert none. On the translate the letters are those
of `w`, so the translated cell inverts exactly when `(i, j)` does — and the cut at the level loses
nothing, because a cell `(i, j) ∈ At(π)` with `j < k` has `i < j` and hence `w i = i < j = w j` by
the prescription, so it is no inversion of `w` either.

## Main results

* `HJO.Dyck.isPartialDyck_prependEast`: `E_kπ ∈ 𝔻_{k+1,n+1}` for a Dyck path `π` of length `n` and
  a level `k ≤ n`.
* `HJO.Dyck.invNumber_prependEast_prependLabel`: the inversion number of the prepended labelling
  against the attack set of the prepended path exceeds that of `w` against `At(π)` by the level `k`.

## Implementation notes

Levels are unshifted while positions, rows, columns, entries and letters are all indexed from `0`,
as in `HJO.Dyck.IsPartialDyck`, `HJO.Dyck.attackSet`, `HJO.Dyck.prependEast` and
`HJO.Dyck.prependLabel`: the level `k` and the length `n` are the paper's, the paper's `x_j` is
`x ⟨j - 1, _⟩ + 1`, the first entry `k + 1` of the paper's `σ^{(k+1)}` is the letter `k`, and its
window `{(i, j) : 1 ≤ i < j ≤ k+1}` is the pairs `i < j` drawn from `{0, …, k}`.

Both clauses of the closure are proved at a `ℕ`-valued position, on the single split `p ≤ k` against
`k < p`, rather than by `Fin.cases`: the second branch is then `HJO.Dyck.prependEast_mk_of_lt`, the
form the definition ships for a position given by an expression rather than by `Fin.succ`.
Monotonicity is accordingly taken in the consecutive form `Fin.monotone_iff_le_succ`, whose two
positions are `Fin.castSucc i` and `Fin.succ i`; their values are `i` and `i + 1`, so the split is
taken on the foot alone, and above the level the two sides of the inequality are the definition's
second clause twice, in its two spellings. The middle monotonicity case `j = k + 1` above, where
`x'_{k+1} = 1` meets `x'_{k+2} = x_{k+1} + 1 ≥ 2`, is not a case here: it falls in the branch whose
foot lies below the level, where the entry is `0` and the head need not be computed at all.

The inversion number is taken in the spelling `HJO.Dyck.partialCharSeries` uses, against the attack
set read as a set of pairs of *positions* —
`{p : Fin N × Fin N | ((p.1 : ℕ), (p.2 : ℕ)) ∈ attackSet x}` — rather than against `attackSet x`
itself, whose index type is `ℕ`. Nothing is lost, every cell of `attackSet x` having both
coordinates below `N`, and this is the form in which `HJO.Dyck.partialCharSeries_prependEast` meets
the exponent of `q`: it is literally the exponent appearing in `HJO.Dyck.normCharSeries`, at `x` on
the right and at `prependEast k x` on the left. `mem_attackSet_prependEast_iff` is the membership
form of that decomposition, `(a, b) ∈ At(E_kπ)` iff `a < b ≤ k` or `(a, b) = (i + 1, j + 1)` for a
cell `(i, j)` of `At(π)` with `j ≥ k`; it is what the case analysis on `Fin (N + 1)` consumes, every
step being a statement about `((p : ℕ), (q : ℕ))` and the shape above being what
`Fin.eq_zero_or_eq_succ` on each coordinate meets. It comes from `HJO.CarlssonMellit.EastAttack`,
where it is proved off `HJO.Dyck.mem_attackSet` and the two value lemmas of `E_k` and carries the
`Finset` equalities of `HJO.Dyck.attackSet_prependEast` and
`HJO.Dyck.attackSet_prependEast_disjoint_union`; it is the pointwise form rather than either
equality that the case analysis here wants.

Hypotheses are weakened to what is spent, and nothing is dead. For the closure the hypothesis
`π ∈ 𝔻_{k,n}` becomes `π ∈ 𝔻_{0,n}` together with `k ≤ n`: the vanishing of the first `k` entries is
dead, because `E_k` discards those entries and replaces them by the `k + 1` virtual north steps of
the new level (`HJO.Dyck.prependEast_congr`, `HJO.Dyck.prependEast_of_le`), while monotonicity and
`x_j ≤ j` are used only above the level. This is strictly stronger and not a decoration of the same
content: `![0, 1, 2] ∉ 𝔻_{2,3}` is a Dyck path of length `3` to which the statement does not apply
at `k = 2`, and `E_2![0, 1, 2] = ![0, 0, 0, 3] ∈ 𝔻_{3,4}` all the same. Dropping `hk` leaves a false
statement — `E_2![0] = ![0, 0]` and `![0, 0] ∉ 𝔻_{3,2}`, the level exceeding the length — and
dropping `h` leaves one too: `![1, 1] ∉ 𝔻_{0,2}` and `E_0![1, 1] = ![0, 2, 2] ∉ 𝔻_{1,3}`, the bound
`x'_2 ≤ 2` failing. For the statistic two of the four hypotheses go the same way: `π ∈ 𝔻_{k,N}` is
weakened to the one part of it that is spent, `k ≤ N`, which is what makes
`#{j : Fin N | j < k} = k`, and `w ∈ U(π, Id_k)` to its prescription half, the no-attack half being
read nowhere — the identity is an equality of two counts neither of which asks the letters at an
attacking pair to differ. A consumer holding `IsPartialDyck k N x` applies these through
`h.toIsSquareDyck` and `h.le_length`, and one holding
`hw : w ∈ HJO.Dyck.noAttackLabellings x (HJO.Dyck.identityTuple k)` supplies the prescription as
`fun i hi => hw.1 i ⟨i, hi⟩ rfl`.

An appeal to `HJO.Dyck.mem_attackSet_of_lt_level` for the rows below the level is not needed
here. The half of its conclusion the argument spends, `(i, j) ∈ At(π) → i < j`, holds of an
arbitrary sequence by `HJO.Dyck.fst_lt_snd_of_mem_attackSet`, the paper's `i ≤ j - 1` being part of
the definition of the attack set rather than a property of a partial Dyck path; the other half,
`i < j → (i, j) ∈ At(π)` for `j < k`, is not used, the argument needing the rows below the level to
carry no inversion rather than to be full.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, arXiv:1508.06239v3, J. Amer. Math.
Soc. **31** (2018) 661--697, Section 4 ("Raising and lowering operators"): "Unlike `𝔻`, the union of
the sets `𝔻_k` over all `k` is closed under the operation of adding a North or East step to the
beginning of the path", and Section 4.3 ("Raising operator"), "Let `π ∈ 𝔻_{k,n}` so that
`Eπ ∈ 𝔻_{k+1,n+1}`" and "We clearly have `inv(Eπ, f(w)) = inv(π, w) + k`". The paper carries no
proposition or proof of the closure and `E` is never given a defining sentence, so the arguments
formalized here are this file's own: lemmas `HJO.Dyck.isPartialDyck_prependEast`, against
`HJO.Dyck.IsSquareDyck`, `HJO.Dyck.IsPartialDyck` and `HJO.Dyck.prependEast`, and
`HJO.Dyck.invNumber_prependEast_prependLabel`, against `HJO.Dyck.attackSet`, `HJO.Dyck.invNumber`,
`HJO.Dyck.IsPartialDyck`, `HJO.Dyck.prependEast`, `HJO.Dyck.noAttackLabellings`,
`HJO.Dyck.identityTuple` and `HJO.Dyck.prependLabel`. Both are consumed by
`HJO.Dyck.partialCharSeries_prependEast`, and the closure also by `HJO.Dyck.attackSet_prependEast`,
`HJO.Dyck.attackSet_prependEast_disjoint_union` and `HJO.Dyck.prependEast_eastInverse`.
-/

@[expose] public section

open Finset

namespace HJO.Dyck

/-! ### Prepending an east step gives a partial Dyck path -/

/-- Prepending an east step to the beginning of a partial Dyck path gives a partial Dyck path one
level longer: `E_kπ ∈ 𝔻_{k+1,n+1}`. Stated for an arbitrary Dyck path `π` of length `n` and a level
`k ≤ n`, the vanishing of the first `k` entries being dead — `E_k` discards them — so the
instance at `h : IsPartialDyck k n x` is
`isPartialDyck_prependEast h.toIsSquareDyck h.le_length`. -/
@[hjo "lem_cm_east_partial"]
theorem isPartialDyck_prependEast {k n : ℕ} {x : Fin n → ℕ} (h : IsSquareDyck n x) (hk : k ≤ n) :
    IsPartialDyck (k + 1) (n + 1) (prependEast k x) := by
  refine ⟨⟨Fin.monotone_iff_le_succ.2 fun i => ?_, fun p => ?_⟩, Nat.succ_le_succ hk,
    fun p hp => prependEast_of_le x (Nat.lt_succ_iff.1 hp)⟩
  -- Monotonicity, at the consecutive positions `i` and `i + 1`.
  · rcases le_or_gt (i : ℕ) k with hik | hik
    -- The foot lies below the level, where the entry is minimal.
    · rw [prependEast_of_le x (by simpa using hik)]
      exact Nat.zero_le _
    -- Both lie above it: `x_{j-1} + 1 ≤ x_j + 1`, by the monotonicity of `x`.
    · rw [prependEast_succ_of_le x hik.le, prependEast_mk_of_lt x i.castSucc.isLt hik]
      exact Nat.succ_le_succ (h.mono (Fin.le_def.2 (by simp)))
  -- The bound above the diagonal: `x'_j ≤ j`.
  · rcases le_or_gt (p : ℕ) k with hp | hp
    -- Below the level the entry is minimal.
    · rw [prependEast_of_le x hp]
      exact Nat.zero_le _
    -- Above it, `x'_j = x_{j-1} + 1 ≤ (j - 1) + 1 = j`.
    · rw [prependEast_mk_of_lt x p.isLt hp]
      have hx : x (⟨(p : ℕ) - 1, by omega⟩ : Fin n) ≤ (p : ℕ) - 1 := h.le_index _
      omega

/-! ### Prepending an east step adds `k` inversions -/

/-- There are `k` positions below the level among `N ≥ k` positions. -/
private theorem card_filter_val_lt {N k : ℕ} (hk : k ≤ N) : #{j : Fin N | (j : ℕ) < k} = k := by
  rw [← Finset.card_range k]
  refine Finset.card_bij (fun j _ => (j : ℕ)) ?_ ?_ ?_
  · intro j hj
    simpa using (Finset.mem_filter.1 hj).2
  · intro a _ b _ h
    exact Fin.val_injective h
  · intro b hb
    exact ⟨⟨b, lt_of_lt_of_le (Finset.mem_range.1 hb) hk⟩,
      by simpa using Finset.mem_range.1 hb, rfl⟩

/-- Prepending an east step to a path and its new special letter to a labelling adds exactly `k`
inversions, the `inv(At(E_kπ), E^*_kw) = inv(At(π), w) + k`: the window of the new
level contributes its `k` pairs `(0, j)`, on which the prepended letter `k` beats each of
`0, 1, …, k - 1`, and the translate of `At(π)` contributes `inv(At(π), w)`, the rows below the level
that the translate drops being uninverted by the prescription. The `π ∈ 𝔻_{k,N}` is
weakened to the one part of it that is used, `k ≤ N`, and its `w ∈ U(π, Id_k)` to the prescription
`w i = i` for `i < k`, the no-attack condition being read nowhere. -/
@[hjo "lem_cm_east_inv"]
theorem invNumber_prependEast_prependLabel {k N : ℕ} (x : Fin N → ℕ) (hk : k ≤ N)
    {w : Fin N → ℕ} (hw : ∀ i : Fin N, (i : ℕ) < k → w i = (i : ℕ)) :
    invNumber {p : Fin (N + 1) × Fin (N + 1) |
        ((p.1 : ℕ), (p.2 : ℕ)) ∈ attackSet (prependEast k x)} (prependLabel k w) =
      invNumber {p : Fin N × Fin N | ((p.1 : ℕ), (p.2 : ℕ)) ∈ attackSet x} w + k := by
  classical
  -- A cell below the level is no inversion of `w`: its two letters are its two coordinates.
  have hlow : ∀ l m : Fin N, ((l : ℕ), (m : ℕ)) ∈ attackSet x → w m < w l → k ≤ (m : ℕ) := by
    intro l m hmem hlt
    by_contra hcon
    have hlm : (l : ℕ) < (m : ℕ) := fst_lt_snd_of_mem_attackSet hmem
    rw [hw l (by omega), hw m (by omega)] at hlt
    omega
  -- The inversion set splits as the window's `k` pairs and the translate of the whole of
  -- `Inv(At(π), w)`.
  have key : invSet {p : Fin (N + 1) × Fin (N + 1) |
        ((p.1 : ℕ), (p.2 : ℕ)) ∈ attackSet (prependEast k x)} (prependLabel k w)
      = (({j : Fin N | (j : ℕ) < k} : Finset (Fin N)).image fun j => ((0 : Fin (N + 1)), j.succ))
        ∪ (invSet {p : Fin N × Fin N | ((p.1 : ℕ), (p.2 : ℕ)) ∈ attackSet x} w).image
            fun p => (p.1.succ, p.2.succ) := by
    refine Finset.ext ?_
    rintro ⟨p, q⟩
    rcases Fin.eq_zero_or_eq_succ p with rfl | ⟨l, rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ q with rfl | ⟨m, rfl⟩ <;>
      simp only [mem_invSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.mem_image, Prod.mk.injEq, Prod.exists, mem_attackSet_prependEast_iff x hk,
        Fin.val_zero, Fin.val_succ, Fin.cons_zero, Fin.cons_succ, Fin.succ_ne_zero,
        Fin.succ_inj]
    -- No cell has its later position at `0`, and no letter beats itself.
    · simp
    -- The window's pairs `(0, j + 1)`: the prepended letter `k` beats `w j = j < k`.
    · constructor
      · rintro ⟨h1 | ⟨i, -, -, -, hi, -⟩, -⟩
        · exact Or.inl ⟨m, by omega, rfl⟩
        · exact absurd hi.symm (Nat.succ_ne_zero i)
      · rintro (⟨a, ha, rfl⟩ | ⟨a, b, -, hF, -⟩)
        · exact ⟨Or.inl ⟨by omega, by omega⟩, by rw [hw a ha]; omega⟩
        · exact hF.elim
    · simp
    -- The translated pairs: the window contributes none of them, `i < j < k` giving `w i < w j`,
    -- and the cut at the level loses no inversion, by `hlow`.
    · constructor
      · rintro ⟨⟨h1, h2⟩ | ⟨i, j, hij, -, hi, hj⟩, hlt⟩
        · rw [hw l (by omega), hw m (by omega)] at hlt
          omega
        · obtain rfl : i = (l : ℕ) := by omega
          obtain rfl : j = (m : ℕ) := by omega
          exact Or.inr ⟨l, m, ⟨hij, hlt⟩, rfl, rfl⟩
      · rintro (⟨a, -, ha, -⟩ | ⟨a, b, ⟨hmem, hlt⟩, rfl, rfl⟩)
        · exact absurd ha.symm (Fin.succ_ne_zero l)
        · exact ⟨Or.inr ⟨(a : ℕ), (b : ℕ), hmem, hlow a b hmem hlt, rfl, rfl⟩, hlt⟩
  have hinjA : Function.Injective fun j : Fin N => ((0 : Fin (N + 1)), j.succ) :=
    fun a b h => Fin.succ_injective _ (congrArg Prod.snd h)
  have hinjB : Function.Injective fun p : Fin N × Fin N => (p.1.succ, p.2.succ) :=
    fun a b h => Prod.ext (Fin.succ_injective _ (congrArg Prod.fst h))
      (Fin.succ_injective _ (congrArg Prod.snd h))
  have hdisj : Disjoint
      (({j : Fin N | (j : ℕ) < k} : Finset (Fin N)).image fun j => ((0 : Fin (N + 1)), j.succ))
      ((invSet {p : Fin N × Fin N | ((p.1 : ℕ), (p.2 : ℕ)) ∈ attackSet x} w).image
        fun p => (p.1.succ, p.2.succ)) := by
    refine Finset.disjoint_left.2 ?_
    rintro ⟨u, v⟩ hu hv
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hu
    obtain ⟨c, -, hc⟩ := Finset.mem_image.1 hv
    rw [Prod.ext_iff] at hj hc
    exact Fin.succ_ne_zero c.1 (hc.1.trans hj.1.symm)
  rw [invNumber, key, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ hinjA, Finset.card_image_of_injective _ hinjB,
    card_filter_val_lt hk, invNumber, Nat.add_comm]

end HJO.Dyck
