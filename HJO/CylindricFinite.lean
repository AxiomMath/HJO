/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Series.Summable
public meta import HJO.Attr

/-! # Finiteness of the cylindric partitions below a volume

Fix `0 < a` and a profile `c`. A cylindric partition of profile `c` whose volume is less than `y`
is very tightly constrained: each of its `a` rows is weakly decreasing, so a nonzero entry at
position `j` forces the whole initial segment of that row to be nonzero and costs the volume at
least `j + 1`; below volume `y` every entry from position `y` on therefore vanishes, and every
entry is itself at most its row sum and hence less than `y`. So such a cylinder is determined by
the `a * y` values it takes on the rows `0, …, a - 1` at the positions `0, …, y - 1`, each of them
one of the `y` numbers below `y`, and there are only finitely many cylinders of volume below `y`.

## Main results

* `HJO.Cylindric.finite_setOf_cylVolume_lt`: for `0 < a` the cylindric partitions of profile `c`
  of volume less than `y` form a finite set.

## Implementation notes

Both halves of the argument are already proved elsewhere in the library and are not reproved here.
`HJO.Summable.finite_setOf_cylVolume_lt` is the counting step — the injection into the functions
`Fin a → Fin y → Fin (N + 1)` given by truncating each entry at the entry bound `N`, its
injectivity supplied by `HJO.Summable.eq_zero_of_cylVolume_le` above position `y` — and it carries
the entry bound. `HJO.Summable.boundedBy_of_cylVolume_lt` is the observation that makes that bound
redundant: a single entry is at most its row sum, which is one of the `a` nonnegative summands of
the volume, so a cylinder of volume less than `y` is already bounded by `y`. The set here is
therefore the `N = y` instance of the bounded one, and what remains is `Set.Finite.subset`.

The entry bound `N` of the bounded form of the statement is dropped rather than assumed, so what is
proved is stronger: the bounded set is a subset of this one for every `N` at once, including the
`N = y - 1` case which is all such a bound ever gives. Volumes and positions are natural numbers, so
the conditions `N ≥ 0` and `y ≥ 0` of the bounded form are automatic and do not appear; at `y = 0`
the set is empty, which the statement covers. The hypothesis `0 < a` is not dead: at `a = 0` the
volume is the empty sum `0`, so for `y = 1` the set contains the infinitely many families whose row
`0` is `(n, 0, 0, …)` and whose other rows vanish.
-/

@[expose] public section

namespace HJO.Cylindric

/-- Only finitely many cylindric partitions have volume below a given bound: for `0 < a` the
cylindric partitions of profile `c` of volume less than `y` form a finite set. Their entries are
automatically less than `y`, so the cylindric partitions of volume less than `y` with all entries
at most `N` are finite too, by `Set.Finite.subset`. -/
@[hjo "lem_bounded_cylinders_finite"]
theorem finite_setOf_cylVolume_lt (a : ℕ) (c : ℕ → ℕ) (y : ℕ) (ha : 0 < a) :
    {l : ℕ → ℕ → ℕ | IsCylindric a c l ∧ cylVolume a l < y}.Finite :=
  (HJO.Summable.finite_setOf_cylVolume_lt a y y c ha).subset fun _l hl =>
    ⟨⟨hl.1, HJO.Summable.boundedBy_of_cylVolume_lt ha hl.1 hl.2⟩, hl.2⟩

end HJO.Cylindric
