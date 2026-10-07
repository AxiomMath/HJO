/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.PartialPaths
public import HJO.CarlssonMellit.Tuples
public meta import HJO.Attr

/-! # Removing and prepending an east step are inverse

The recursion of the paper's Section 4 moves between the levels by adding a step to the beginning
of a partial Dyck path, and the east half of its step is read backwards: the recursion is stated
through `E_k`, which prepends an east step, while the path it is applied to is produced by `D_k`,
which deletes one. This file records that the second undoes the first on the paths whose first step
really is east: `E_k(D_{k+1}(π)) = π` for a sequence whose entries below the level `k + 1` are
minimal and whose entries from the level on are not.

## Main results

* `HJO.Dyck.prependEast_eastInverse`: `E_{k-1}(D_k(π)) = π`.

## Implementation notes

Levels are unshifted while positions and entries are indexed from `0`, as in
`HJO.Dyck.IsPartialDyck`: the level is `k + 1` and its length `n + 1`, the spelling of
`HJO.Dyck.isPartialDyck_eastInverse`, so that `D_k(π)` is `HJO.Dyck.eastInverse (k + 1) x` at the
level `k` and length `n` with no truncated subtraction, `E_{k-1}` is `HJO.Dyck.prependEast k`, and
the `k ≥ 1` is structural rather than a hypothesis. The paper's entry `x_j` is
`x ⟨j - 1, _⟩ + 1`, so its `x_j = 1` reads `x p = 0` and its `x_j ≥ 2` reads `0 < x j`.

The two hypotheses are exactly the two things the entrywise comparison spends, and the full
`π ∈ 𝔻_{k+1,n+1}` together with "`k = N` or `x_{k+1} ≥ 2`" is not assumed, because only these two
consequences of it are read. `hlow` is the level condition, `HJO.Dyck.IsPartialDyck` at the level
`k + 1` read through `eq_zero_of_lt_level`: it settles the positions `p ≤ k`, where `E_k` writes the
minimal entry of the new level and reads no sequence at all. `hx` is the positivity of every entry
from the level on, the same hypothesis as in
`HJO.Dyck.partialStepWord_succ_eq_D_cons_partialStepWord_eastInverse`, and it is what makes the
remaining positions agree: `E_k` raises by one what `D_{k+1}` lowered by one, and the lowering is a
truncated subtraction, so the two cancel exactly where the entry is nonzero. It is the shape the
full condition takes once monotonicity is spent — given `Monotone x` and `k + 1 ≤ n + 1`,
the disjunction `k + 1 = n + 1 ∨ 0 < x ⟨k+1, _⟩` gives it, the first branch vacuously and the second
by monotonicity — so of the data only `HJO.Dyck.IsSquareDyck.mono` and
`IsPartialDyck.le_length` and `eq_zero_of_lt_level` are read, the diagonal bound being dead.

Neither hypothesis is weakenable, and both are recovered from the conclusion, so the pair is
equivalent to it: `HJO.Dyck.prependEast_of_le` makes every entry of the left-hand side at a position
`p ≤ k` minimal, which is `hlow`, and `HJO.Dyck.prependEast_succ_of_le` makes every later entry a
successor, which is `hx`. So `hx` in particular cannot be dropped: at `k = 0` on `![0, 0]`, whose
entry at the level is minimal, `D_1` truncates rather than shifting and `E_0(D_1(π)) = ![0, 1]` is
not `π`.

The statement is an equality of sequences and not of members of `𝔻_{k+1,n+1}`, both maps being
total; a consumer wanting the membership of the left-hand side has it from that of the right by
`rfl` after this rewrite, and the membership of `D_{k+1}(π)` itself is
`HJO.Dyck.isPartialDyck_eastInverse`.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, arXiv:1508.06239v3,
J. Amer. Math. Soc. **31** (2018) 661--697, Section 4:
the union of the sets `𝔻_k` is closed under adding a north or an east step to the beginning of the
path, and every Dyck path is built that way from the empty path of `𝔻_0`; and `π ∈ 𝔻_{k,n}` gives
`Eπ ∈ 𝔻_{k+1,n+1}`, the step whose inverse on such paths is recorded here. The lemma
`HJO.Dyck.prependEast_eastInverse` consumes `HJO.Dyck.IsPartialDyck`, `HJO.Dyck.prependEast`,
`HJO.Dyck.eastInverse` and `HJO.Dyck.isPartialDyck_eastInverse`.
-/

@[expose] public section

namespace HJO.Dyck

/-- **Removing and prepending an east step are inverse.** For a
sequence whose entries below the level `k + 1` are minimal — the paper's `x_1 = ⋯ = x_{k+1} = 1` —
and whose entries from the level on are not — the paper's `k = N` or `x_{k+1} ≥ 2`, which
monotonicity turns into the positivity of every later entry — prepending an east step to
`D_{k+1}(π)` returns `π`: the `E_{k-1}(D_k(π)) = π`.

Positions `p ≤ k` are minimal on both sides by `HJO.Dyck.prependEast_of_le` and `hlow`, and at a
position `l + 1 ≥ k + 1` the raising of `HJO.Dyck.prependEast_succ_of_le` undoes the truncated
lowering of `HJO.Dyck.eastInverse_of_le`, which is where `hx` is spent. -/
@[hjo "lem_cm_east_inverse_recover"]
theorem prependEast_eastInverse {k n : ℕ} {x : Fin (n + 1) → ℕ}
    (hlow : ∀ p : Fin (n + 1), (p : ℕ) < k + 1 → x p = 0)
    (hx : ∀ j : Fin (n + 1), k + 1 ≤ (j : ℕ) → 0 < x j) :
    prependEast k (eastInverse (k + 1) x) = x := by
  refine funext fun p => ?_
  induction p using Fin.cases with
  | zero => rw [prependEast_zero]; exact (hlow 0 (Nat.succ_pos k)).symm
  | succ l =>
    rcases le_or_gt ((l : ℕ) + 1) k with hl | hl
    · rw [prependEast_of_le _ (show ((l.succ : Fin (n + 1)) : ℕ) ≤ k by simpa using hl)]
      exact (hlow l.succ (by simp only [Fin.val_succ]; omega)).symm
    · have hpos : 0 < x l.succ := hx l.succ (by simp only [Fin.val_succ]; omega)
      rw [prependEast_succ_of_le _ (show k ≤ (l : ℕ) by omega),
        eastInverse_of_le _ (show k + 1 ≤ (l : ℕ) + 1 by omega)]
      omega

end HJO.Dyck
