/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepComputesClosed

/-! # `HJO.Mellit.SweepAppend` at a generic parameter, and the remaining shuffle-side hypothesis

`HJO.Mellit.SweepAppend` is **false at `q = 1`** (`HJO.Mellit.not_sweepAppend_one_left`) and true at
the one instance that has been evaluated at every other scalar
(`HJO.Mellit.sweepAppend_nil_one_one_two`), so every use of it has to be made at a generic
parameter. This file writes the two equivalences of `HJO/Shuffle/SweepWitnessAppend.lean` in that
form, and composes them with the assembly so that the remaining hypothesis of the shuffle side is
stated in terms of a *generic* `SweepAppend`.

## Neither direction of either equivalence needs a hypothesis on `q`

`HJO.Mellit.mellitInduction_sweepWitness_iff_sweepAppend` and
`HJO.Mellit.braidClosedForm_sweepWitness_iff_sweepAppend` are hypothesis-free, and that is
**correct in both directions**: they are equivalences between two propositions *about one and the
same `q`*, and their proof — `HJO.Mellit.mellitInduction_iff_braidClosedForm`,
`HJO.Mellit.isBraidValue_sweepWitness_iff`, `HJO.Mellit.sweepIn_injective` — spends only
`Nat.Coprime a b`, `0 < a`, `0 < b`. Adding `q ≠ 1` to either one would weaken a true statement and
buy nothing: a per-`q` equivalence cannot carry genericity, because the quantifier that genericity
lives in is outside it.

What is needed is the statement in which the quantifier appears, and it is supplied here twice:

* `HJO.Mellit.forall_mellitInduction_sweepWitness_iff_forall_sweepAppend` and
  `HJO.Mellit.forall_braidClosedForm_sweepWitness_iff_forall_sweepAppend` — the two equivalences
  with `q ≠ 1` quantified over on both sides, where the hypothesis is not decoration: at `q = 1`
  the right-hand side is refuted by `HJO.Mellit.not_sweepAppend_one_left` and the left-hand side by
  `HJO.Mellit.not_mellitInduction_sweepWitness_one_left`, so the unrestricted forms of both sides
  are false and the equivalence of the restricted ones is the only usable reading.
* `HJO.Mellit.shuffle_of_lhs_and_sweepAppend` — `HJO.External.Shuffle L` from `LhsComputes` and a
  generic `SweepAppend`, the `q ≠ 1` being free where it is used, by
  `HJO.Mellit.sub_one_ne_zero_of_algebraicIndependent_fst`.

## Which hypothesis: `q ≠ 1`, and why the algebraic independence is needed

`q ≠ 1` is what is added, in both the quantified equivalences and the obligation of
`HJO.Mellit.shuffle_of_lhs_and_sweepAppend`: it is exactly what the refutation at `q = 1` excludes,
it is what `HJO.Mellit.sweepAppend_nil_one_one_two` proves the identity under, and it is free where
the clause is used, which is only under `AlgebraicIndependent ℤ ![q, u]`. It is **not** enough for
the obligation, however: `HJO.Mellit.SweepAppend` also fails at `q = 0` and at `u = 0`
(`HJO.Mellit.not_sweepAppend_nil_two_three_one_of_q_zero`,
`HJO.Mellit.not_sweepAppend_nil_two_three_one_of_u_zero`), so the hypothesis of
`HJO.Mellit.shuffle_of_lhs_and_sweepAppend` is unsatisfiable.
`HJO.Mellit.shuffle_of_lhs_and_sweepAppend_of_algebraicIndependent` states the weaker obligation,
under the full independence, and that is the true remaining hypothesis.

Nothing downstream is disturbed: the hypothesis-free equivalences are untouched and still exported,
which is what `HJO/Shuffle/SweepAppendRefuted.lean` transports the falsity through.
-/

@[expose] public section

namespace HJO.Mellit

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The two equivalences with the quantifier that carries the genericity -/

/-- **`HJO.Mellit.BraidClosedForm` at the witness, generically in `q`.** The `q ≠ 1` of
`HJO.Mellit.not_sweepAppend_one_left` quantified over on both sides of
`HJO.Mellit.braidClosedForm_sweepWitness_iff_sweepAppend`, which is where a hypothesis on the
parameter can sit: the per-`q` equivalence is true without it and cannot use it. Both sides of the
*unrestricted* statement are false, so this is the reading in which the equivalence has content. -/
theorem forall_braidClosedForm_sweepWitness_iff_forall_sweepAppend :
    (∀ q u : L, q ≠ 1 → ∀ a b : ℕ, Nat.Coprime a b → 0 < a → 0 < b →
        BraidClosedForm (sweepWitness q u a b) a b)
      ↔ ∀ q u : L, q ≠ 1 → ∀ a b : ℕ, Nat.Coprime a b → 0 < a → 0 < b → SweepAppend q u a b :=
  ⟨fun h q u hq a b hab ha hb =>
      (braidClosedForm_sweepWitness_iff_sweepAppend hab ha hb).1 (h q u hq a b hab ha hb),
    fun h q u hq a b hab ha hb =>
      (braidClosedForm_sweepWitness_iff_sweepAppend hab ha hb).2 (h q u hq a b hab ha hb)⟩

/-- **`HJO.Mellit.mellitInduction_sweepWitness` at the witness, generically in `q`.** The companion
of `HJO.Mellit.forall_braidClosedForm_sweepWitness_iff_forall_sweepAppend` through
`HJO.Mellit.mellitInduction_sweepWitness_iff_sweepAppend`. This is the statement a proof of the
generic `HJO.Mellit.SweepAppend` is carried to `HJO.Mellit.MellitInduction` by. -/
theorem forall_mellitInduction_sweepWitness_iff_forall_sweepAppend :
    (∀ q u : L, q ≠ 1 → ∀ a b : ℕ, Nat.Coprime a b → 0 < a → 0 < b →
        MellitInduction (sweepWitness q u a b) a b)
      ↔ ∀ q u : L, q ≠ 1 → ∀ a b : ℕ, Nat.Coprime a b → 0 < a → 0 < b → SweepAppend q u a b :=
  ⟨fun h q u hq a b hab ha hb =>
      (mellitInduction_sweepWitness_iff_sweepAppend hab ha hb).1 (h q u hq a b hab ha hb),
    fun h q u hq a b hab ha hb =>
      (mellitInduction_sweepWitness_iff_sweepAppend hab ha hb).2 (h q u hq a b hab ha hb)⟩

/-! ### The hypothesis is free where it is used -/

/-- **`q ≠ 1` from the algebraic independence**, in the form the assembly's quantifier hands it
over: `HJO.Mellit.sub_one_ne_zero_of_algebraicIndependent_fst` read as a statement about `q` rather
than about `q - 1`. -/
theorem ne_one_of_algebraicIndependent_fst {K : Type*} [Field K] {q u : K}
    (hqu : AlgebraicIndependent ℤ ![q, u]) : q ≠ 1 :=
  sub_ne_zero.1 (sub_one_ne_zero_of_algebraicIndependent_fst hqu)

/-- **`HJO.Mellit.mellitInduction_sweepWitness` at the witness, in exactly the shape
`HJO.Mellit.shuffle_of_lhs_and_induction` asks for it, from a generic `HJO.Mellit.SweepAppend`.**
The `AlgebraicIndependent ℤ ![q, u]` of the use site supplies `q ≠ 1`, and its `1 < a < b` supplies
the `0 < a`, `0 < b` the equivalence spends; the coprimality is passed
straight through. So the `q ≠ 1` the identity is missing costs the assembly nothing. -/
theorem mellitInduction_sweepWitness_of_sweepAppend
    (hsa : ∀ q u : L, q ≠ 1 → ∀ a b : ℕ, Nat.Coprime a b → 0 < a → 0 < b → SweepAppend q u a b) :
    ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b →
      MellitInduction (sweepWitness q u a b) a b :=
  fun q u hqu a b hab ha hb =>
    (mellitInduction_sweepWitness_iff_sweepAppend hab (by omega) (by omega)).2
      (hsa q u (ne_one_of_algebraicIndependent_fst hqu) a b hab (by omega) (by omega))

/-! ### The remaining hypothesis of the shuffle side -/

/-- **`HJO.External.Shuffle` from `LhsComputes` and a generic `HJO.Mellit.SweepAppend`.**
`HJO.Mellit.shuffle_of_lhs_and_induction` reduces the shuffle side to `LhsComputes` and
`HJO.Mellit.MellitInduction` at the witness; the second of those becomes an identity about
`HJO.Mellit.dsc`.

**The hypothesis of this lemma is unsatisfiable; the usable form is
`HJO.Mellit.shuffle_of_lhs_and_sweepAppend_of_algebraicIndependent`.** `q ≠ 1` is not all that
`HJO.Mellit.SweepAppend` needs: it also fails at `q = 0` and at `u = 0` as soon as `2 ≤ a`:

* `HJO.Mellit.not_sweepAppend_nil_two_three_one_of_q_zero`
  (`HJO/Shuffle/SweepAppendTwoThree.lean`) refutes an instance of `SweepAppend q u 2 3` at
  `q = 0`, which satisfies `q ≠ 1`;
* `HJO.Mellit.not_sweepAppend_nil_two_three_one_of_u_zero` does the same at `u = 0`.

The mechanism is the one behind two other clauses of this reduction: the type-`C` event at `(0,1)`
carries `q⁻¹` and the `z` letter of the slope word carries `(qu)⁻¹`, and `0⁻¹ = 0` in a field. It is
**absent at `a = 1`, `A = 1`**, where no event has a live step to its right and the slope word has
no `z` letter, which is why `HJO.Mellit.sweepAppend_nil_one_one_b` needs only `q ≠ 1`; at `A ≥ 2`
the scalar `(qu)^{1-A}` vanishes at `qu = 0` for every `a`
(`HJO/Shuffle/SweepAppendNilDegenerate.lean`).

So `hsa` below asks for something false. The statement is kept because it records the shape of the
reduction; the usable form is the `AlgebraicIndependent` one below, where `q ≠ 0`, `q ≠ 1` and
`u ≠ 0` are all free. -/
theorem shuffle_of_lhs_and_sweepAppend
    (hlhs : ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ a b : ℕ, Nat.Coprime a b → 1 < a →
      a < b → LhsComputes q u a b)
    (hsa : ∀ q u : L, q ≠ 1 → ∀ a b : ℕ, Nat.Coprime a b → 0 < a → 0 < b → SweepAppend q u a b) :
    HJO.External.Shuffle L :=
  shuffle_of_lhs_and_induction hlhs (mellitInduction_sweepWitness_of_sweepAppend hsa)

/-- **The same reduction with the weakest obligation**, `HJO.Mellit.SweepAppend` asked for only
under the hypotheses the assembly itself carries. This is the true remaining hypothesis of the
shuffle side; `HJO.Mellit.shuffle_of_lhs_and_sweepAppend` asks for more, and its hypothesis is
unsatisfiable (see there). -/
theorem shuffle_of_lhs_and_sweepAppend_of_algebraicIndependent
    (hlhs : ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ a b : ℕ, Nat.Coprime a b → 1 < a →
      a < b → LhsComputes q u a b)
    (hsa : ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ a b : ℕ, Nat.Coprime a b → 1 < a →
      a < b → SweepAppend q u a b) :
    HJO.External.Shuffle L :=
  shuffle_of_lhs_and_induction hlhs fun q u hqu a b hab ha hb =>
    (mellitInduction_sweepWitness_iff_sweepAppend hab (by omega) (by omega)).2
      (hsa q u hqu a b hab ha hb)

end HJO.Mellit

end
