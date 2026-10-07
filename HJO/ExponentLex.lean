/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Finsupp.Lex
public meta import HJO.Attr

/-! # The lexicographic order on exponent vectors is a strict total order

The leading-term and triangularity arguments for the Macdonald polynomials maximize an exponent
vector along the lexicographic comparison `Finsupp.Lex (· < ·) (· < ·)`, which needs that
comparison to be a strict total order.

Mathlib has this, but on the type synonym `Lex (σ →₀ N)` rather than on `σ →₀ N`: the instance
`Finsupp.Lex.linearOrder` makes the synonym a linear order whose `<` is, by definition, the
relation `Finsupp.Lex (· < ·) (· < ·)` on the underlying finitely supported functions. Transporting
it back to the bare type is therefore `inferInstanceAs` across the synonym, and nothing has to be
proved.

## Main results

* `Finsupp.isStrictTotalOrder_lex`: `Finsupp.Lex (· < ·) (· < ·)` is a strict total order
  on `σ →₀ N`.
-/

@[expose] public section

/-- The lexicographic comparison of exponent vectors is a strict total order: the relation
`Finsupp.Lex (· < ·) (· < ·)`, which holds of `α` and `β` when the entry of `α` is the smaller at
the least index where the two differ, is irreflexive and transitive and relates any two distinct
exponent vectors in exactly one of the two directions. -/
@[hjo "lem_mac_lex_total"]
theorem Finsupp.isStrictTotalOrder_lex {σ N : Type*} [LinearOrder σ] [Zero N] [LinearOrder N] :
    IsStrictTotalOrder (σ →₀ N) (Finsupp.Lex (· < ·) (· < ·)) :=
  inferInstanceAs (IsStrictTotalOrder (Lex (σ →₀ N)) (· < ·))
