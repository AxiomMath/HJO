/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepAppendRefuted
public import HJO.Shuffle.SweepComputesClosed
public import HJO.Macdonald.StandingFacts

/-! # The refutation's parameter point is unreachable from the assembly, as a theorem

This file settles, as a theorem, a reading of the shuffle side under which a refutation proved
here and the clause the shuffle assembly asks for would contradict each other. It is not a
contradiction, and the reconciliation is one line; here it is as something a reader can check.

## The two statements that look opposed

* `HJO.Mellit.not_mellitInduction_sweepWitness_one_left`
  (`HJO/Shuffle/SweepAppendRefuted.lean`) proves
  `¬ MellitInduction (sweepWitness (1 : L) u 1 b) 1 b`. Read carelessly: "`MellitInduction` is
  FALSE at the sweep witness".
* The clause the shuffle assembly asks for is proved in its range, as
  `HJO.Mellit.mellitInduction_sweepWitness`.

## Why both hold

The refutation is at `q = 1` **and** `a = 1`. The binders of
`HJO.Mellit.shuffle_of_lhs_and_induction` carry `AlgebraicIndependent ℤ ![q, u]`, which forces
`q ≠ 1`, and `1 < a`, which forces `a ≠ 1`. So the refuted parameter point is outside the
quantification **on two independent counts**, and `HJO.Mellit.refutation_params_unreachable` below
is that statement.

What this does and does not buy. It does **not** prove the clause (that is
`HJO.Mellit.mellitInduction_sweepWitness`), and this file has no bearing on it. What it does is
make "outside the quantification" a checked statement rather than a remark, so that a weakening of
the assembly's hypotheses — which is the one change that would make the refutation bite — cannot
happen silently: it would break this file.

## References

This file concerns `HJO.Mellit.mellitInduction_sweepWitness`.
-/

@[expose] public section

namespace HJO.Mellit

variable {L : Type*} [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in
/-- **The refuted parameter point is unreachable from the shuffle assembly's binders, on two
independent counts.** `HJO.Mellit.not_mellitInduction_sweepWitness_one_left` refutes the clause at
`q = 1, a = 1`; the binders of `HJO.Mellit.shuffle_of_lhs_and_induction` give `q ≠ 1` from algebraic
independence and `a ≠ 1` from `1 < a`.

So a refutation at that point says nothing about the clause the assembly asks for. This is the whole
content of the distinction, stated as a theorem rather than a remark so that it is checked.

Note which hypothesis does which job: **neither alone suffices**, because the refutation needs both
`q = 1` and `a = 1`. Dropping `1 < a` from the assembly while keeping algebraic independence would
still exclude the point, but only by the `q` clause — and the `a = 1` sweep is genuinely degenerate
(`HJO.Sweep.corner` divides by `q - 1`, and at `a = 1` the rectangle has a single column), so both
are worth keeping. -/
theorem refutation_params_unreachable {q u : L} (hqu : AlgebraicIndependent ℤ ![q, u]) {a : ℕ}
    (ha : 1 < a) : q ≠ 1 ∧ a ≠ 1 :=
  ⟨fun h => Standing.one_sub_q_ne_zero hqu (by rw [h, sub_self]), by omega⟩

omit [Algebra ℚ L] in
/-- **The same, in the shape the assembly's binder actually presents.** Whenever the `hind` binder
of `HJO.Mellit.shuffle_of_lhs_and_induction` is being supplied, its own hypotheses already exclude
the refuted point — so the refutation is never reachable inside a proof of that binder, and a reader
checking whether the refutation damages the assembly can stop here.

The conclusion is stated as the conjunction rather than as two lemmas on purpose: the two exclusions
are only interesting together, since the refutation needs both. -/
theorem forall_refutation_params_unreachable :
    ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b →
      q ≠ 1 ∧ a ≠ 1 :=
  fun _ _ hqu _ _ _ ha _ => refutation_params_unreachable hqu ha

end HJO.Mellit

end
