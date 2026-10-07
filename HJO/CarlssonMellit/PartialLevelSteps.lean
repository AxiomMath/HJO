/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.SquareDyck
public import HJO.CarlssonMellit.Tuples
public meta import HJO.Attr

/-! # The level of a partial Dyck path, and the first step of a nonempty one

The recursion of Carlsson and Mellit reads a partial Dyck path by peeling its first step, and
Carlsson and Mellit record that the union of the sets `𝔻_{k,n}` is closed under adding a north or an
east step to the beginning of the path. Four facts about the level are what that recursion needs,
and this file proves them.

Under the encoding of `HJO.Dyck.IsPartialDyck` a partial path from `(0, k)` to `(n, n)` is recorded
as the square Dyck path of length `n` whose first `k` entries are minimal, the level being carried
as a parameter rather than read off the sequence. Adding a north step at the beginning therefore
moves no entry: it only changes the level at which the sequence is read. So two of the four facts
are inclusions of sets of sequences and one is an equality of such sets; only the east case moves
the sequence, through `HJO.Dyck.eastInverse`.

## Main results

* `HJO.Dyck.IsPartialDyck.of_le_level`: `𝔻_{k,n} ⊆ 𝔻_{j,n}` for `j ≤ k`, the operation of
  adding north steps at the beginning of the path.
* `HJO.Dyck.isPartialDyck_succ_iff`: `𝔻_{k+1,n}` is the set of paths of `𝔻_{k,n}` whose next step
  is north.
* `HJO.Dyck.IsSquareDyck.xor_exists_apply_eq_zero_level_pos`: the first step of a nonempty partial
  path is north or east and not both.
* `HJO.Dyck.isPartialDyck_eastInverse`: deleting the leading east step lands in `𝔻_{k-1,n-1}`.

## Implementation notes

Levels, positions and entries are indexed from `0` throughout, as in `HJO.Dyck.IsPartialDyck`: the
entry `x_j` of the `1`-based coarea notation is `x (j - 1) + 1`, so its lower bound `x_j ≥ 1` is
vacuous, while the level is unshifted, being a count of rows rather than an index into them.

Three of the four statements are strictly stronger than their first-written forms, and in each case
the strengthening removes a hypothesis this encoding makes idle rather than weakening anything.

`of_le_level` is stated for an arbitrary lower level `j ≤ k` rather than for `k - 1`, which removes
both the `k ≥ 1` — dead once `k - 1` is replaced by `j`, since `j ≤ k` covers `j = k` —
and the truncated subtraction. The instance is `h.of_le_level (Nat.sub_le k 1)`.

`isPartialDyck_succ_iff` is an equivalence, not just one implication; the converse
is the two clauses of `IsPartialDyck` read backwards at the level `k + 1`, and the equivalence is
what lets the recursion rewrite a sum over `𝔻_{k+1,n}` as a sum over a subset of `𝔻_{k,n}`.

`isPartialDyck_eastInverse` drops two of the hypotheses. The level condition `x_1 = ⋯ = x_k = 1` is
spent nowhere: the initial entries of `D_k(π)` are placed by `HJO.Dyck.eastInverse_of_lt`, whose
value is `0` and mentions no sequence, so `D_k` lands in `𝔻_{k-1,n-1}` from every square Dyck path.
The condition "`k = N` or `x_{k+1} ≥ 2`", which says that the path's first step really is east, is
spent, in the `1`-based integer formulation, on its lower bound `x'_j ≥ 1` and on the junction
`x'_{k-1} = 1 ≤ x_{k+1} - 1 = x'_k` of monotonicity; both fall to the shift of the minimum entry
from `1` to `0`, which turns them into `0 ≤ x'_j` and `0 ≤ x'_k`. That is a genuine asymmetry and
not a licence to forget the condition: `HJO.Dyck.eastInverse` agrees with the map `D_k` of the
integer formulation, which is defined on sequences of *integers*, only where the condition holds —
at `π = (1, 1, 1) ∈ 𝔻_{2,3}` that formula gives `x'_1 = 1 > 0 = x'_2`, while the truncated
subtraction here returns `0` and the conclusion survives. So the statement below is about
`eastInverse`, and a consumer wanting the integer map `D_k` must supply the condition itself.

`xor_exists_apply_eq_zero_level_pos` carries `0 < n` where the integer formulation carries
`2N - k ≥ 1`. The two agree under `k ≤ N`, since `2N - k ≥ N`; the corner the side condition rules
out is `k = N = 0`, and phrasing it as `0 < n` makes the position `⟨0, hn⟩` exist unconditionally,
so the `k = 0` branch needs no case split on `k < N` versus `k = N`. Of the path hypothesis only
`le_index` at the origin is spent, and the level condition of `IsPartialDyck` not at all, so the
statement is made about a square Dyck path; the first alternative is a proof-indexed existential
rather than a conjunction `k < n ∧ x ⟨k, _⟩ = 0` so that destructuring hands a consumer the bound
and the equation together.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*,
J. Amer. Math. Soc. **31** (2018) 661--697, Section 4, "the union of the sets `𝔻_k` over all `k` is
closed under the operation of adding a North or East step to the beginning of the path".
-/

@[expose] public section

namespace HJO.Dyck

/-! ### Lowering the level -/

/-- **Prepending north steps to a partial Dyck path.** A partial Dyck path
of level `k` is a partial Dyck path of every level `j ≤ k`, which under the encoding of
`HJO.Dyck.IsPartialDyck` moves no entry and lowers only the level at which the sequence is read.
The one-step case `𝔻_{k,n} ⊆ 𝔻_{k-1,n}` is `h.of_le_level (Nat.sub_le k 1)`, and
`j = 0` reads a partial path of any level as a Dyck path of length `n`. -/
@[hjo "lem_cm_north_partial"]
theorem IsPartialDyck.of_le_level {k n : ℕ} {x : Fin n → ℕ} (h : IsPartialDyck k n x) {j : ℕ}
    (hj : j ≤ k) : IsPartialDyck j n x :=
  ⟨h.toIsSquareDyck, hj.trans h.le_length,
    fun l hl => h.eq_zero_of_lt_level l (hl.trans_le hj)⟩

/-! ### Raising the level at a north step -/

/-- A property holding at every position of `Fin n` below `k + 1` holds at every position below `k`
and at the position `k` itself, and conversely: the positions below `k + 1` are the positions below
`k` together with `⟨k, hk⟩`. This is the one step of mathematics in `isPartialDyck_succ_iff`, where
the property is the vanishing of an entry. -/
private theorem forall_val_lt_succ_iff {k n : ℕ} (hk : k < n) {p : Fin n → Prop} :
    (∀ l : Fin n, (l : ℕ) < k + 1 → p l) ↔ (∀ l : Fin n, (l : ℕ) < k → p l) ∧ p ⟨k, hk⟩ := by
  refine ⟨fun h => ⟨fun l hl => h l (Nat.lt_succ_of_lt hl), h _ (Nat.lt_succ_self k)⟩,
    fun h l hl => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hlk | hlk
  · exact h.1 l hlk
  · obtain rfl : l = ⟨k, hk⟩ := Fin.ext hlk
    exact h.2

/-- **Raising the level at a north step.** `𝔻_{k+1,n}` is the set of partial Dyck paths of level `k`
whose next step is north: for `k < n`, a sequence lies in `𝔻_{k+1,n}` exactly when it lies in
`𝔻_{k,n}` and its `(k+1)`-st entry is minimal, `x_{k+1} = 1` in `1`-based notation, which on entries
indexed from `0` reads `x ⟨k, hk⟩ = 0`.

The implication is the `←` direction. The hypothesis `k < n` is spent on `←` alone,
`IsPartialDyck.le_length` at the level `k + 1` supplying it on `→`; it cannot be traded for a
condition quantified over the positions `l` with `(l : ℕ) = k`, that variant being false at `k = n`,
where it is vacuous while `𝔻_{n+1,n}` is empty. -/
@[hjo "lem_cm_north_level"]
theorem isPartialDyck_succ_iff {k n : ℕ} {x : Fin n → ℕ} (hk : k < n) :
    IsPartialDyck (k + 1) n x ↔ IsPartialDyck k n x ∧ x ⟨k, hk⟩ = 0 := by
  rw [isPartialDyck_iff_of_le hk, isPartialDyck_iff_of_le hk.le, forall_val_lt_succ_iff hk,
    and_assoc]

/-! ### The first step of a nonempty partial path -/

/-- The first entry of a square Dyck path is minimal, `x_1 = 1` in `1`-based notation: the diagonal
bound at the origin reads `x ⟨0, hn⟩ ≤ 0`. This is the only part of the Dyck condition that the
dichotomy on the first step spends. -/
private theorem apply_zero_of_isSquareDyck {n : ℕ} {x : Fin n → ℕ} (h : IsSquareDyck n x)
    (hn : 0 < n) : x ⟨0, hn⟩ = 0 :=
  Nat.le_zero.1 (h.le_index ⟨0, hn⟩)

/-- **The first step of a nonempty partial Dyck path.** Read at any level `k`, a nonempty square
Dyck path either has a next entry and that entry is minimal — in `1`-based notation `k < N` and
`x_{k+1} = 1`, a north step — or the level is positive and no next entry is minimal — `k ≥ 1`
together with "`k = N` or `x_{k+1} ≥ 2`", an east step — and not both.

The `k = N` disjunct of the second alternative is the vacuous case of its bounded quantifier, so no
case split on it appears. The side condition `2N - k ≥ 1` is `0 < n` here: the two agree
under `k ≤ N`, and phrasing it this way makes the position `⟨0, hn⟩` exist without a case split. -/
@[hjo "lem_cm_path_dichotomy"]
theorem IsSquareDyck.xor_exists_apply_eq_zero_level_pos {k n : ℕ} {x : Fin n → ℕ}
    (h : IsSquareDyck n x) (hn : 0 < n) :
    Xor (∃ hkn : k < n, x ⟨k, hkn⟩ = 0) (0 < k ∧ ∀ hkn : k < n, 0 < x ⟨k, hkn⟩) := by
  by_cases hnorth : ∃ hkn : k < n, x ⟨k, hkn⟩ = 0
  · obtain ⟨hkn, hx⟩ := hnorth
    refine Or.inl ⟨⟨hkn, hx⟩, fun heast => ?_⟩
    have := heast.2 hkn
    omega
  · refine Or.inr ⟨⟨?_, fun hkn => ?_⟩, hnorth⟩
    · by_contra hk
      have hk0 : k = 0 := by omega
      subst hk0
      exact hnorth ⟨hn, apply_zero_of_isSquareDyck h hn⟩
    · by_contra hx
      exact hnorth ⟨hkn, by omega⟩

/-! ### Removing a leading east step -/

/-- **Removing a leading east step gives a partial Dyck path.** `D_{k+1}(π) ∈ 𝔻_{k,n}` for every
square Dyck path `π` of length `n + 1` and every level `k ≤ n`, that is, `D_k(π) ∈ 𝔻_{k-1,N-1}` with
`k` the level of `π`.

The two branches of `HJO.Dyck.eastInverse` match the two Dyck conditions one for one: monotonicity
comes from `IsSquareDyck.mono` alone, its junction free because the first branch holds the minimum,
and the diagonal bound from `IsSquareDyck.le_index` alone. The level hypothesis and its
condition "`k = N` or `x_{k+1} ≥ 2`" are both idle here, for the reasons recorded in this file's
implementation notes — the second because the minimum entry is `0` rather than `1`, so the junction
asks nothing. -/
@[hjo "lem_cm_east_inverse_partial"]
theorem isPartialDyck_eastInverse {k n : ℕ} {x : Fin (n + 1) → ℕ}
    (h : IsSquareDyck (n + 1) x) (hk : k ≤ n) :
    IsPartialDyck k n (eastInverse (k + 1) x) := by
  refine ⟨⟨fun a b hab => ?_, fun l => ?_⟩, hk, fun l hl => eastInverse_of_lt _ (by omega)⟩
  · rcases lt_or_ge ((b : ℕ) + 1) (k + 1) with hb | hb
    · have hab' : (a : ℕ) ≤ (b : ℕ) := hab
      rw [eastInverse_of_lt _ (show (a : ℕ) + 1 < k + 1 by omega), eastInverse_of_lt _ hb]
    · rcases lt_or_ge ((a : ℕ) + 1) (k + 1) with ha | ha
      · rw [eastInverse_of_lt _ ha]
        exact Nat.zero_le _
      · have hab' : (a : ℕ) ≤ (b : ℕ) := hab
        have hx : x a.succ ≤ x b.succ :=
          h.mono (show a.succ ≤ b.succ from Fin.le_def.2 (by simp only [Fin.val_succ]; omega))
        rw [eastInverse_of_le _ ha, eastInverse_of_le _ hb]
        omega
  · rcases lt_or_ge ((l : ℕ) + 1) (k + 1) with hl | hl
    · rw [eastInverse_of_lt _ hl]
      exact Nat.zero_le _
    · have hle : x l.succ ≤ (l : ℕ) + 1 := by
        have := h.le_index l.succ
        simpa only [Fin.val_succ] using this
      rw [eastInverse_of_le _ hl]
      omega

end HJO.Dyck
