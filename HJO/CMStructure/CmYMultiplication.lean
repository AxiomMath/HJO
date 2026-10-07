/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.AtildeCorner
public import HJO.CMStructure.CmReplemma
public meta import HJO.Attr

/-! # The corner elements act on `V_*` as multiplication by the variables

**A step the proof of `HJO.Sweep.exists_linearEquiv_e0Ideal` needs.** The proof of
`HJO.Sweep.exists_linearEquiv_e0Ideal` reduces a word of `e_k𝔸_qe_0` to a normal form in the corner
elements `y_i` of `HJO.Dyck.Aq.yElt` and the arrows, and then reads the result off as one of the
elements `y_1^{a_1}⋯y_k^{a_k}B_{a_{k+1}+1}(⋯)` of `HJO.Sweep.exists_basis_vstar_prod_bop`. That last
reading needs to know what the ALGEBRA element `y_i` DOES on `V_*` under the action of
`HJO.Sweep.exists_isDpaAction_cm`, namely that it is multiplication by the variable `y_i` on `V_k`
and `0` on every other summand. The lemma of that shape, `HJO.Sweep.map_yElt_eq_auxMulPiece`, is
about the MODIFIED action, and `HJO.Sweep.exists_isDpaAction_cm` does not contain the step either:
the header of `HJO/CMStructure/CmReplemma.lean` records that "the remark that `y_1, …, y_k` act by
multiplication is not part of this statement and is not proved here".

Almost all of the content is already available, at one remove. `HJO.Sweep.yOpVstar_eq_loopVstar`
says that the corner family built DIRECTLY out of the unstarred operators on `V_*` is multiplication
by the variable, and `HJO.Dyck.Aq.cornerOf_eq_yElt` says that `HJO.Dyck.Aq.yElt` is that same
generic construction read in `𝔸_q`. What remains is the one step between them: an action is an
algebra map, `HJO.Dyck.map_cornerOf` transports the construction along any algebra map, and so an
action carrying the four generator families to the unstarred families on `V_*` carries `y_i` to
`HJO.Sweep.yOpVstar`. This file is that step and its two consequences.

## Main results

* `HJO.Sweep.map_yElt_eq_yOpVstar` — an action agreeing with the unstarred families on the arrows,
  the loops and the idempotents sends `HJO.Dyck.Aq.yElt` to `HJO.Sweep.yOpVstar`.
* `HJO.Sweep.map_yElt_eq_auxMulPiece_cm` — and therefore to multiplication by `y_i` on `V_k`, and
  `0` elsewhere. This is `HJO.Sweep.map_yElt_eq_auxMulPiece` for Carlsson and Mellit's own action,
  the shape `HJO.Sweep.exists_linearEquiv_e0Ideal` reads its normal form in.
* `HJO.Sweep.exists_isDpaAction_cm_yElt` — `HJO.Sweep.exists_isDpaAction_cm`'s action, with that
  clause added, so a later proof obtains the corner clause from the same existential rather than
  re-deriving it.

## Implementation notes

**Nothing here is a second corner family.** `HJO.Sweep.yOpVstar` already exists and is already known
to be multiplication by the variable; the content of this file is that the action's value on the
algebra's own `y_i` is that operator, which is a transport and not a computation. Stating it the
other way round — defining a new operator on `V_*` and proving the relations again — would be the
duplication `HJO.Sweep.yOpVstar` was written to avoid.

**The two invertibility hypotheses are inherited, not added.** `HJO.Dyck.Aq.yElt` divides by `q - 1`
and inverts the Hecke generators, so `HJO.Dyck.Aq.yElt` does not exist without `Invertible q` and
`Invertible (q - 1)`; `HJO.Sweep.exists_isDpaAction_cm` itself carries no condition on `q`. Any
statement mentioning a corner element carries these two, here as everywhere else in this library.

## Related declarations

The definition `HJO.Dyck.Aq.yElt`, the action `HJO.Sweep.exists_isDpaAction_cm`, and the proof of
`HJO.Sweep.exists_linearEquiv_e0Ideal`, which uses this step. The modified-action counterpart is
`HJO.Sweep.map_yElt_eq_auxMulPiece`.
-/

@[expose] public section

namespace HJO.Sweep

section Cm

variable {L : Type*} [Field L] [Algebra ℚ L] {q : L} [Invertible q] [Invertible (q - 1)]
  {ρ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)}

/-- **An action agreeing with the unstarred families carries `y_i` to `HJO.Sweep.yOpVstar`.** Both
sides are `HJO.Dyck.cornerOf` at the same three scalars, one read in `𝔸_q` and one in
`End_𝕜(V_*)`, so the identity is `HJO.Dyck.map_cornerOf` at the algebra map `ρ`: the corner elements
are built from the generators by multiplication and scalars alone, and an algebra map preserves
both. -/
theorem map_yElt_eq_yOpVstar (hact : IsDpaAction q ρ)
    (hT : ∀ k i : ℕ, ρ (Dyck.Aq.Tg L q k i) = loopVstar (braidModPiece q) k i)
    (hD : ∀ k : ℕ, ρ (Dyck.Aq.dMinus L q k) = lowerVstar (dminusPiece q) k)
    (hU : ∀ k : ℕ, ρ (Dyck.Aq.dPlus L q k) = raiseVstar (cmDPlusPiece q) k) (k i : ℕ) :
    ρ (Dyck.Aq.yElt L q k i) = yOpVstar q k i := by
  rw [← Dyck.Aq.cornerOf_eq_yElt]
  exact Dyck.map_cornerOf (f := ρ) (E := Dyck.Aq.e L q) (U := Dyck.Aq.dPlus L q)
    (D := Dyck.Aq.dMinus L q) (T := Dyck.Aq.Tg L q) (E' := pieceProj L)
    (U' := raiseVstar (cmDPlusPiece q)) (D' := lowerVstar (dminusPiece q))
    (T' := loopVstar (braidModPiece q)) q ⅟q ⅟(q - 1) hact.map_e hU hD hT k i

/-- **The corner elements of `𝔸_q` act as multiplication by the variables**, for Carlsson and
Mellit's own action: for `1 ≤ i ≤ k` the operator `ρ(y_i)` is multiplication by `y_i` on `V_k` and
`0` on every other summand. This is the step the proof of `HJO.Sweep.exists_linearEquiv_e0Ideal`
reads its normal form off with, and `HJO.Sweep.map_yElt_eq_auxMulPiece` for the unstarred action in
place of the modified one. -/
theorem map_yElt_eq_auxMulPiece_cm (hact : IsDpaAction q ρ)
    (hT : ∀ k i : ℕ, ρ (Dyck.Aq.Tg L q k i) = loopVstar (braidModPiece q) k i)
    (hD : ∀ k : ℕ, ρ (Dyck.Aq.dMinus L q k) = lowerVstar (dminusPiece q) k)
    (hU : ∀ k : ℕ, ρ (Dyck.Aq.dPlus L q k) = raiseVstar (cmDPlusPiece q) k)
    {k i : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) :
    ρ (Dyck.Aq.yElt L q k i) = loopVstar (auxMulPiece L) k i := by
  rw [map_yElt_eq_yOpVstar hact hT hD hU k i, yOpVstar_eq_loopVstar q h1 hik]

/-- **`HJO.Sweep.exists_isDpaAction_cm`'s action, with the corner clause.** The four clauses are
`HJO.Sweep.exists_isDpaAction_cm` verbatim; the fifth is
`HJO.Sweep.map_yElt_eq_auxMulPiece_cm`. A proof that needs to know what a normal form in the
corner elements does on `V_*` — `HJO.Sweep.exists_linearEquiv_e0Ideal` is the one — takes it from
here. -/
theorem exists_isDpaAction_cm_yElt (q : L) [Invertible q] [Invertible (q - 1)] :
    ∃ ρ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L), IsDpaAction q ρ
      ∧ (∀ k i : ℕ, ρ (Dyck.Aq.Tg L q k i) = loopVstar (braidModPiece q) k i)
      ∧ (∀ k : ℕ, ρ (Dyck.Aq.dMinus L q k) = lowerVstar (dminusPiece q) k)
      ∧ (∀ k : ℕ, ρ (Dyck.Aq.dPlus L q k) = raiseVstar (cmDPlusPiece q) k)
      ∧ ∀ k i : ℕ, 1 ≤ i → i ≤ k →
          ρ (Dyck.Aq.yElt L q k i) = loopVstar (auxMulPiece L) k i := by
  obtain ⟨ρ, hact, hT, hD, hU⟩ := exists_isDpaAction_cm (L := L) q
  exact ⟨ρ, hact, hT, hD, hU, fun k i h1 hik =>
    map_yElt_eq_auxMulPiece_cm hact hT hD hU h1 hik⟩

end Cm

end HJO.Sweep

end
