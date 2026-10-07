/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.NoAttack
public import HJO.CarlssonMellit.PartialPaths
public import HJO.CarlssonMellit.Tuples
public meta import HJO.Attr

/-! # Prepending a label is a bijection of labellings

The raising step of the Carlsson--Mellit recursion prepends an east step to a partial Dyck path
`π ∈ 𝔻_{k,N}`, giving `E_kπ ∈ 𝔻_{k+1,N+1}`, and prepends the new special letter `k+1` to a
labelling of `π`, giving `E^*_kw`. This file carries the combinatorial heart of that step:
`E^*_k` is a bijection from the labellings `U(π, Id_k)` prescribed by the identity tuple onto the
labellings `U(E_kπ, σ^{(k+1)})` prescribed by the cyclic tuple `σ^{(k+1)} = (k+1, 1, …, k)`, so the
sum defining `ν_{σ^{(k+1)}}(E_kπ)` may be reindexed by `U(π, Id_k)`.

Both halves are forced by the shape of `At(E_kπ)`, and the half that carries them is about the
positions rather than the letters: the new position attacks exactly the prescribed window,
`(0, j + 1) ∈ At(E_kπ)` if and only if `j < k`, its rows below the level being full because they
carry the `k + 1` virtual north steps, while above the level row `j + 1` of `At(E_kπ)` begins at
`x_j + 1`, so it is the translate of row `j` of `At(π)`. So the new letter meets prescribed
positions only, where `σ^{(k+1)}` keeps it distinct — the paper's "this is possible because `1`
does not attack `k+1` in `Eπ`" — and above the level it is free to repeat and does: at `k = 1`,
`π = ![0, 0]`, the labelling `![0, 1]` of `U(π, Id_1)` has image `![1, 0, 1] ∈ U(E_1π, σ^{(2)})`,
carrying the new letter `1` again at the position `2` it does not attack.

## Main results

* `HJO.Dyck.bijOn_prependLabel_noAttackLabellings`: `E^*_k` is a bijection from `U(π, Id_k)` onto
  `U(E_kπ, σ^{(k+1)})`, for an arbitrary sequence `x` and with no relation between `k` and `N`.

## Implementation notes

Positions and letters are both indexed from `0`, as for `HJO.Dyck.noAttackLabellings`,
`HJO.Dyck.prependEast` and `HJO.Dyck.prependLabel`, so the paper's prepended letter `k+1` is the
letter `k` and its tuple `σ^{(k+1)} = (k+1, 1, …, k)` is `(k, 0, …, k-1)`, which is the last
member `HJO.Dyck.cycleTuple (Fin.last k)` of the family `σ^{(i)}` of length `k+1`. The two
prescribed tuples are the values of one and the same map,
`prependLabel k (identityTuple k) = cycleTuple (Fin.last k)`, by
`HJO.Dyck.cycleTuple_last_eq_prependLabel_identityTuple`; rewriting with it reduces the whole
lemma to one about `Fin.cons k`, where `Fin.cons_zero` and `Fin.cons_succ` read both prescriptions
and both labellings off a single case split on each position.

All of `At(E_kπ)` is read through one lemma,
`mem_attackSet_prependEast_succ`: a cell of `At(E_kπ)` in the row `j + 1` is one with
`(if j < k then 0 else x_j + 1) ≤ i < j + 1`, which is `HJO.Dyck.mem_attackSet_coe` with the two
branches of `E_k` left unsplit. Its two consequences are the two halves of the bijection. At
`i = 0` it says the new position attacks the row `j + 1` exactly when `j < k`, since `x_j + 1 ≤ 0`
is false, and there the prescription gives the letter `j < k` against the new letter `k`. At
`i = l + 1` it says the cell is the translate of `(l, j) ∈ At(π)` once `j ≥ k`, and for `j < k`
both positions are prescribed and carry their own indices; conversely a cell of `At(π)` translates,
both branches of the `if` being at most `l + 1`. So the route through
`HJO.Dyck.attackSet_prependEast` and `HJO.Dyck.attackSet_prependEast_disjoint_union` is not taken,
and the cells of `At(E_kπ)` outside the square `{0, …, N}²` — which those two descriptions get wrong
once `k > N` — never arise.

The conclusion is `Set.BijOn`, carrying the paper's two halves as `Set.MapsTo` and `Set.SurjOn`,
together with a `Set.InjOn` that names no datum of it: `prependLabel k` is `Fin.cons k`, injective
by `Fin.cons_succ`, so `Set.InjOn (prependLabel k) S` holds for an arbitrary `S`. It is what the
call site takes, in this orientation: `finsum_mem_eq_of_bijOn` reindexes any summand along it, and
`HJO.Dyck.coeff_normCharSeries_eq_finsum` reads a coefficient as the unrestricted
`∑ᶠ w ∈ U(π, σ)`, so this lemma gives `HJO.Dyck.partialCharSeries_prependEast` the index side alone,
its summand identity being `HJO.Dyck.invNumber_prependEast_prependLabel` for the exponent and
`HJO.Sym.insertFront_zvar` for the monomial. No `Finset` form composes there: each side is infinite
exactly when `k < N`, a free position above the level admitting a letter past every one used.

The whole of the situation is dropped, none of it being used: `π` is an arbitrary
sequence rather than a partial Dyck path, and there is no relation between the level and the length,
where one might ask `N ≥ k`. The sets of labellings read `π` only through `At(π)`
(`HJO.Dyck.noAttackLabellings_congr`), so neither monotonicity of the path, nor `x_j ≤ j`, nor the
minimality of its first `k` entries is spent; and the row-by-row reading above never compares the
level with the length. What the absence of `k ≤ N` buys is a consumer's discharge rather than
combinatorial reach, since for `N ≤ k` the prescription clause of `HJO.Dyck.noAttackLabellings`
quantifies over every position and `U(π, Id_k)` collapses to the singleton `{Fin.val}`; a consumer
holding `IsPartialDyck k N x` applies this lemma with nothing to discharge.

Only the injectivity of the target's prescribed tuple is spent on `Id_k`, and only by the
`Set.MapsTo` half: `Set.SurjOn (prependLabel k)` between the corresponding sets holds at an
arbitrary `σ : Fin k → ℕ` with no hypothesis at all, as `Set.InjOn` does. The entity is stated at
the paper's own tuples for the consumer's spelling — `HJO.Dyck.partialCharSeries_prependEast`
applies `HJO.Dyck.partialCharSeries` at `σ^{(k+1)}` and reads that tuple's being a permutation of
the labels off `HJO.Dyck.cycleTuple_lt_and_injective` — so a statement at a general `σ` would carry
the target as `prependLabel k σ` and put that identity at every call site.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, arXiv:1508.06239v3, J. Amer. Math.
Soc. **31** (2018) 661--697, Section 4.3 ("Raising operator"): the bijection
`f : U_{π,Id_k} → U_{Eπ,σ}` with `σ = (k+1, 1, …, k)`, which prepends the letter `k+1` to a
labelling and whose being well defined the paper reads off one non-attack, "this is possible
because 1 does not attack k+1 in Eπ", with the surrounding discussion of `Eπ ∈ 𝔻_{k+1,n+1}`
and the definition of `U_{π,σ}`. The lemma is `HJO.Dyck.bijOn_prependLabel_noAttackLabellings`,
against `HJO.Dyck.IsPartialDyck`, `HJO.Dyck.prependEast`, `HJO.Dyck.noAttackLabellings`,
`HJO.Dyck.identityTuple`, `HJO.Dyck.cycleTuple` and `HJO.Dyck.prependLabel`, consumed by
`HJO.Dyck.partialCharSeries_prependEast`.
-/

@[expose] public section

namespace HJO.Dyck

/-- A cell of `At(E_kπ)` in a row after the first: row `j + 1` of the attack set of the prepended
path is the interval `{e, …, j}` beginning at the entry `e = (if j < k then 0 else x_j + 1)` of
`E_kπ` there. This is `mem_attackSet_coe` at the position `Fin.succ j` with the two branches of
`E_k` left unsplit, and it is the only reading of `At(E_kπ)` the bijection makes: at `i = 0` it
says the new position attacks exactly the rows below the level, and at `i = l + 1` it identifies
the cells above the level with the translates of the cells of `At(π)`. -/
private theorem mem_attackSet_prependEast_succ {k N : ℕ} (x : Fin N → ℕ) (i : ℕ) (j : Fin N) :
    (i, (j : ℕ) + 1) ∈ attackSet (prependEast k x) ↔
      (if (j : ℕ) < k then 0 else x j + 1) ≤ i ∧ i < (j : ℕ) + 1 := by
  rw [← Fin.val_succ j, mem_attackSet_coe, prependEast_succ]

/-- Prepending the new special letter is a bijection of labellings: for any sequence `x` of length
`N` and any level `k`, the map `E^*_k` of `HJO.Dyck.prependLabel` is a bijection from the no-attack
labellings `U(π, Id_k)` of `π = x` prescribed by the identity tuple onto the no-attack labellings
`U(E_kπ, σ^{(k+1)})` of the path got by prepending an east step, prescribed by the cyclic tuple
`σ^{(k+1)} = (k+1, 1, …, k)`, which is `cycleTuple (Fin.last k)` with letters indexed from `0`.
The `π ∈ 𝔻_{k,N}` and `N ≥ k` are both dropped, neither being used: the labellings read
`At(π)` only at pairs of positions of the path, which is where the sibling descriptions of
`At(E_kπ)` spend `k ≤ N` and this bijection does not. -/
@[hjo "lem_cm_east_bijection"]
theorem bijOn_prependLabel_noAttackLabellings {k N : ℕ} (x : Fin N → ℕ) :
    Set.BijOn (prependLabel k) (noAttackLabellings x (identityTuple k))
      (noAttackLabellings (prependEast k x) (cycleTuple (Fin.last k))) := by
  rw [cycleTuple_last_eq_prependLabel_identityTuple]
  refine ⟨fun w hw => ⟨?_, ?_⟩, ?_, ?_⟩
  -- The prescription transports: the new letter sits at the new position, and the letters of `w`
  -- prescribed by `Id_k` are those of `E^*_kId_k` one position later.
  · intro p j hpj
    induction p using Fin.cases with
    | zero =>
      obtain rfl : j = 0 := Fin.ext hpj.symm
      rfl
    | succ l =>
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨m, rfl⟩
      · simp at hpj
      · simpa using hw.1 l m (by simpa using hpj)
  -- The no-attack condition transports. The new position attacks only the rows below the level,
  -- where the prescription keeps the letters apart; every other cell is the translate of a cell of
  -- `At(π)`, or lies below the level at both ends.
  · intro p q hpq
    rcases Fin.eq_zero_or_eq_succ p with rfl | ⟨l, rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ q with rfl | ⟨m, rfl⟩
    · exact absurd (fst_lt_snd_of_mem_attackSet hpq) (by simp)
    -- `(0, m + 1) ∈ At(E_kπ)` forces `m < k`, where `w m = m < k` and the new letter is `k`.
    · rw [Fin.val_zero, Fin.val_succ, mem_attackSet_prependEast_succ] at hpq
      obtain ⟨h1, -⟩ := hpq
      have hmk : (m : ℕ) < k := by
        split_ifs at h1 with h
        · exact h
        · omega
      simp only [prependLabel, Fin.cons_zero, Fin.cons_succ, hw.1 m ⟨(m : ℕ), hmk⟩ rfl]
      exact Nat.ne_of_gt hmk
    · exact absurd (fst_lt_snd_of_mem_attackSet hpq) (by simp)
    · rw [Fin.val_succ, Fin.val_succ, mem_attackSet_prependEast_succ] at hpq
      obtain ⟨h1, h2⟩ := hpq
      have hlm : (l : ℕ) < (m : ℕ) := by omega
      simp only [prependLabel, Fin.cons_succ]
      rcases lt_or_ge (m : ℕ) k with hmk | hmk
      -- Both positions lie below the level, where the prescription gives them their own indices.
      · rw [hw.1 l ⟨(l : ℕ), by omega⟩ rfl, hw.1 m ⟨(m : ℕ), hmk⟩ rfl]
        exact Nat.ne_of_lt hlm
      -- Above the level the cell is the translate of `(l, m) ∈ At(π)`.
      · refine hw.2 l m (mem_attackSet_coe.2 ⟨?_, hlm⟩)
        split_ifs at h1 with h
        · omega
        · omega
  -- Injectivity: `E^*_k` is `Fin.cons k`, and a labelling is recovered from its value at the
  -- positions after the first.
  · intro w _ w' _ h
    refine funext fun l => ?_
    simpa using congrFun h l.succ
  -- Surjectivity: a labelling of the target carries the new letter at the new position, so it is
  -- the image of its own tail, which lies in the source.
  · intro v hv
    refine ⟨Fin.tail v, ⟨?_, ?_⟩, ?_⟩
    · intro l m hlm
      simpa [Fin.tail, prependLabel] using hv.1 l.succ m.succ (by simpa using hlm)
    · intro l m hlm
      obtain ⟨hx, hlt⟩ := mem_attackSet_coe.1 hlm
      refine hv.2 l.succ m.succ ?_
      rw [Fin.val_succ, Fin.val_succ, mem_attackSet_prependEast_succ]
      refine ⟨?_, by omega⟩
      split
      · exact Nat.zero_le _
      · omega
    · refine funext fun p => ?_
      rcases Fin.eq_zero_or_eq_succ p with rfl | ⟨l, rfl⟩
      · simpa [prependLabel] using (hv.1 0 0 rfl).symm
      · simp [Fin.tail, prependLabel]

end HJO.Dyck
