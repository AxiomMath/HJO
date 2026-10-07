/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Prod.Lex
public import Mathlib.Order.Interval.Finset.Nat
public meta import HJO.Attr

/-! # The super alphabet

The expansion of the characteristic series that Carlsson and Mellit use runs over words in a
doubled alphabet: each letter carries an absolute value and a sign, the paper's `ℤ_+ ∪ ℤ_-` with
its letter `ā` the negative letter of absolute value `a`. This file fixes that alphabet.

## Main definitions

* `HJO.Sym.SuperLetter`: the alphabet `𝒜`.
* `HJO.Sym.SuperLetter.absVal`, `HJO.Sym.SuperLetter.IsNegative`: the absolute value and the sign.

## Implementation notes

The alphabet is the *lexicographic* product `ℕ ×ₗ Bool`, not the plain product: the paper's order
`1 < 1̄ < 2 < 2̄ < ⋯` compares absolute values first and breaks a tie by putting the positive letter
below the negative one, which is exactly `Prod.Lex` with `false` reading as positive, `Bool`'s own
order having `false < true`. So the `LinearOrder` and the `DecidableEq` of the alphabet are
`Mathlib`'s, and nothing about the order has to be built: `SuperLetter.lt_iff` is the paper's
definition read off the instance, and the three-term `SuperLetter.chain` checks it.

Absolute values are indexed from `0`, as every letter of this library is, so the paper's
letter `a ≥ 1` has absolute value `a - 1` here and the paper's `x_a` is the letter
`MvPowerSeries.X (a - 1)` of the alphabet. The paper's positivity `a ≥ 1` is therefore vacuous,
which is why `ℕ` and not `ℕ+` is the absolute-value type: a subtype would carry a proof through
every tuple, sort and monomial of the expansion and buy nothing, the bound never being used.

## References

E. Carlsson and A. Mellit, *A proof of the
shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 3.
-/

@[expose] public section

namespace HJO.Sym

/-- **The super alphabet** `𝒜 = ℤ_{>0} × \{1, -1\}`: a letter is an absolute value together with a
sign. Realised as the lexicographic product `ℕ ×ₗ Bool`, with absolute values indexed from `0` and
the sign `false` reading as positive, so that the paper's order
`1 < 1̄ < 2 < 2̄ < ⋯` — compare absolute values, and at equal absolute values put the positive
letter first — is the `LinearOrder` of `Prod.Lex`. -/
@[hjo "def_cm_super_alphabet"]
abbrev SuperLetter : Type := ℕ ×ₗ Bool

namespace SuperLetter

/-- The letter with absolute value `a` and the given sign, `false` being positive. -/
def mk (a : ℕ) (neg : Bool) : SuperLetter := toLex (a, neg)

/-- **The absolute value of a letter**: the `a` in `α = (a, ε)`, indexed from `0`. -/
@[hjo "def_cm_super_alphabet"]
def absVal (α : SuperLetter) : ℕ := (ofLex α).1

/-- **The sign of a letter**, as a `Bool`: `true` is the sign `ε = -1` and `false` the sign
`ε = 1`. -/
@[hjo "def_cm_super_alphabet"]
def IsNegative (α : SuperLetter) : Prop := (ofLex α).2 = true

/-- **A letter is positive** when its sign is `ε = 1`. -/
@[hjo "def_cm_super_alphabet"]
def IsPositive (α : SuperLetter) : Prop := (ofLex α).2 = false

instance instDecidableIsNegative (α : SuperLetter) : Decidable (IsNegative α) := by
  unfold IsNegative; infer_instance

instance instDecidableIsPositive (α : SuperLetter) : Decidable (IsPositive α) := by
  unfold IsPositive; infer_instance

@[simp]
theorem absVal_mk (a : ℕ) (neg : Bool) : absVal (mk a neg) = a := rfl

/-- The sign a letter built from an absolute value and a sign carries is that sign. With
`absVal_mk` this says that `mk` is a section of the two accessors, which is what lets a consumer
read `IsPositive` and `IsNegative` off a constructed letter. -/
@[simp]
theorem sign_mk (a : ℕ) (neg : Bool) : (ofLex (mk a neg)).2 = neg := rfl

/-- Every letter is positive or negative, and not both: the sign takes the two values
`1` and `-1`. -/
theorem isPositive_iff_not_isNegative (α : SuperLetter) : IsPositive α ↔ ¬IsNegative α := by
  rw [IsPositive, IsNegative, Bool.not_eq_true]

/-- A letter is determined by its absolute value and its sign. -/
theorem ext {α β : SuperLetter} (habs : absVal α = absVal β)
    (hsign : (ofLex α).2 = (ofLex β).2) : α = β :=
  congrArg toLex (Prod.ext habs hsign)

/-- **The order on the super alphabet**: `α ≺ β` when the absolute value of `α` is smaller, or the
absolute values agree and `α` is positive while `β` is negative. This is the order
`1 < 1̄ < 2 < 2̄ < ⋯` verbatim, and it is a *theorem* rather than a definition: the relation
is the `<` of `Mathlib`'s `Prod.Lex` linear order on `ℕ ×ₗ Bool`, so it is a strict total order with
nothing to prove (`lt_trichotomy`, `lt_trans` and `DecidableEq` all come from the instance), and
this lemma is the identification of that `<` with the paper's prescription. -/
@[hjo "def_cm_super_order"]
theorem lt_iff {α β : SuperLetter} :
    α < β ↔ absVal α < absVal β ∨ (absVal α = absVal β ∧ IsPositive α ∧ IsNegative β) := by
  rw [Prod.Lex.lt_iff]
  refine or_congr .rfl (and_congr .rfl ?_)
  rw [IsPositive, IsNegative, Bool.lt_iff]

/-- Two letters of different absolute value are compared by their absolute values alone: the
order refines the order on absolute values. -/
@[hjo "def_cm_super_order"]
theorem lt_of_absVal_lt {α β : SuperLetter} (h : absVal α < absVal β) : α < β :=
  lt_iff.2 (Or.inl h)

/-- The positive letter of an absolute value lies below the negative one: the paper's `a < ā`, the
tie-break of `HJO.Sym.SuperLetter.lt_iff`. -/
@[hjo "def_cm_super_order"]
theorem mk_false_lt_mk_true (a : ℕ) : mk a false < mk a true :=
  lt_iff.2 (Or.inr ⟨rfl, sign_mk a false, sign_mk a true⟩)

/-- A value check of the order at the paper's own first three letters: `1 < 1̄ < 2`, which reads
`(0, +) < (0, -) < (1, +)` here. This pins the tie-break and the precedence together: ordering the
sign first would put `(1, +)` below `(0, -)`, and putting the negative letter first at equal
absolute value would reverse the first step. -/
theorem chain : mk 0 false < mk 0 true ∧ mk 0 true < mk 1 false :=
  ⟨mk_false_lt_mk_true 0, lt_of_absVal_lt Nat.zero_lt_one⟩

/-- **The order is a strict total order**, which the paper asserts: any two letters are comparable,
and no letter is below itself. Both are the `LinearOrder` instance of `Prod.Lex`, so the assertion
costs nothing beyond naming it — which is the whole reason the alphabet is the lexicographic
product and not the plain one. -/
@[hjo "def_cm_super_order"]
theorem lt_trichotomy' (α β : SuperLetter) : α < β ∨ α = β ∨ β < α :=
  lt_trichotomy α β

end SuperLetter

end HJO.Sym
