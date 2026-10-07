/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CornerPowers
public import HJO.CarlssonMellit.SweepCM
public meta import HJO.Attr

/-! # An action of the Dyck path algebra on the graded module

`HJO.Sweep.exists_slopeActions` produces, for each coprime pair `(m, n)`, a pair of *actions* of the
Dyck path algebra on `V_*`. `HJO.Sweep.IsDpaAction` says what an action is: a `𝕜`-algebra
homomorphism `ρ : B → End_𝕜(V_*)`, where `B` is `𝔸_q` or `𝔸_{q^{-1}}`, such that `ρ(𝟏_k)` is the
projection of `V_* = ⨁_j V_j` onto its `k`-th summand, for every `k ≥ 0`.

This is the bridge `HJO.Sweep.exists_slopeActions` needs: it is what carries the abstract-algebra
corner results — `HJO.Dyck.Aq.yElt_mul_dMinus`, `HJO.Dyck.Aq.dPlus_mul_yElt`,
`HJO.Dyck.Aq.yElt_comm` and the rest — across to the operators on `V_*`.

## Main definitions

* `HJO.Sweep.pieceProj` — the projection of `V_*` onto its `k`-th summand as an endomorphism of
  `V_*`, which is the `e_k` read as an element of `End_𝕜(V_*)`.
* `HJO.Sweep.IsDpaAction`.

## Main results

* `HJO.Sweep.pieceProj_mul_pieceProj`, `HJO.Sweep.pieceProj_mul_pieceProj_of_ne` — the projections
  are orthogonal idempotents, so an algebra map satisfying `HJO.Sweep.IsDpaAction`'s clause is
  forced to respect the two incidence relations `𝟏_k𝟏_k = 𝟏_k` and `𝟏_k𝟏_l = 0` of `HJO.Dyck.Aq`.
* `HJO.Sweep.IsDpaAction.eq_pieceProj_mul_mul_pieceProj` — the remark after
  `HJO.Sweep.IsDpaAction`: an action carries a path from `j` to `k` to an endomorphism vanishing on
  every summand but `V_j` and landing in `V_k`.

## Implementation notes

**One definition covers both algebras.** The usual "let `B` be either `𝔸_q` or
`𝔸_{q^{-1}}`" is a case distinction only because it writes the two algebras as different objects;
here `HJO.Dyck.Aq` takes its parameter `q` explicitly and `HJO.Dyck.AqInv K q` *is*
`HJO.Dyck.Aq K ⅟q` (`HJO.Dyck.AqInv`), so `HJO.Sweep.IsDpaAction` is stated for
`HJO.Dyck.Aq L q'` at a free `q'` and the two clauses of the definition are its instances at
`q' = q` and `q' = ⅟q`. Nothing is weakened: an action of `𝔸_{q^{-1}}` in the sense above
is exactly `IsDpaAction (⅟q) ρ`.

**`ρ(1) ≠ ∑_k ρ(𝟏_k)`, and that is correct.** `HJO.Dyck.Aq` is a quotient of a free algebra and so
is unital, with `1` not the sum of the idempotents `𝟏_k` — an infinite sum, which the algebra does
not have. `HJO.Sweep.IsDpaAction` asks for a homomorphism of *unital* `𝕜`-algebras, which is what
`→ₐ[L]` records, and separately for the values on the `𝟏_k`; the two conditions are independent and
both are imposed.

**The projection is `ofPiece ∘ toPiece`, not a `Submodule` coercion.** `HJO.Sweep.Vstar` is the
direct sum `⨁_k pieceSub k`, whose summands are independent even though the pieces themselves are
nested (`HJO.Sweep.piece_mono`); `HJO.Sweep.toPiece` is `DirectSum.component` and
`HJO.Sweep.ofPiece` is `DirectSum.lof`, so their composite is the idempotent of the `k`-th summand
and `HJO.Sweep.pieceProj_mul_pieceProj_of_ne` is the independence.

## References

Definition `HJO.Sweep.IsDpaAction`, using `HJO.Sweep.Vstar`, `HJO.Dyck.Aq` and `HJO.Dyck.AqInv`;
consumed by `HJO.Sweep.IsIntertwinedPair`, `HJO.Sweep.exists_isDpaAction_replication`,
`HJO.Sweep.exists_isDpaAction_mod`, `HJO.Sweep.exists_isDpaAction_mellit` and
`HJO.Sweep.exists_slopeActions`. Transcribing A. Mellit, *Toric braids and `(m, n)`-parking
functions*, §3.2.
-/

@[expose] public section

namespace HJO.Sweep

section Proj

variable {L : Type*} [CommRing L]

/-- **The projection of `V_*` onto its `k`-th summand**, as an endomorphism of `V_*`: the idempotent
`e_k` read inside `End_𝕜(V_*)`, which is where `HJO.Sweep.IsDpaAction` reads it. It is the composite
of `HJO.Sweep.toPiece` and `HJO.Sweep.ofPiece`. -/
noncomputable def pieceProj (L : Type*) [CommRing L] (k : ℕ) : Module.End L (Vstar L) :=
  (ofPiece L k) ∘ₗ (toPiece L k)

@[simp]
theorem pieceProj_apply (k : ℕ) (x : Vstar L) : pieceProj L k x = ofPiece L k (toPiece L k x) := rfl

@[simp]
theorem pieceProj_ofPiece (k : ℕ) (F : pieceSub L k) :
    pieceProj L k (ofPiece L k F) = ofPiece L k F := by
  rw [pieceProj_apply, toPiece_ofPiece]

@[simp]
theorem pieceProj_ofPiece_of_ne {k l : ℕ} (h : l ≠ k) (F : pieceSub L l) :
    pieceProj L k (ofPiece L l F) = 0 := by
  rw [pieceProj_apply, toPiece_ofPiece_of_ne h, map_zero]

/-- **The projections are idempotent**, which is the relation `𝟏_k𝟏_k = 𝟏_k` of `HJO.Dyck.Aq` on the
other side of an action. -/
theorem pieceProj_mul_pieceProj (k : ℕ) :
    pieceProj L k * pieceProj L k = pieceProj L k := by
  refine LinearMap.ext fun x => ?_
  change pieceProj L k (pieceProj L k x) = pieceProj L k x
  rw [pieceProj_apply k x, pieceProj_ofPiece]

/-- **The projections are orthogonal**, which is `𝟏_k𝟏_l = 0` for `k ≠ l`. -/
theorem pieceProj_mul_pieceProj_of_ne {k l : ℕ} (h : l ≠ k) :
    pieceProj L k * pieceProj L l = 0 := by
  refine LinearMap.ext fun x => ?_
  change pieceProj L k (pieceProj L l x) = 0
  rw [pieceProj_apply l x, pieceProj_ofPiece_of_ne h]

end Proj

/-! ### The definition -/

section Action

variable {L : Type*} [CommRing L] {q' : L}

/-- **An action of the Dyck path algebra on the graded module.** `HJO.Sweep.IsDpaAction`:
for `B` either `𝔸_q` or `𝔸_{q^{-1}}`, an action of `B` on `V_*` is a `𝕜`-algebra homomorphism `ρ`
from `B` to the `𝕜`-algebra of `𝕜`-linear endomorphisms of `V_*` such that `ρ(𝟏_k)` is the
projection onto the summand `V_k` for every `k ≥ 0`.

The algebra-homomorphism half is carried by the type of `ρ`; this structure is the remaining clause.
The two choices of `B` are the two instances `q' = q` and `q' = ⅟q` of the free
parameter, `HJO.Dyck.AqInv K q` being `HJO.Dyck.Aq K ⅟q` by `HJO.Dyck.AqInv`. -/
@[hjo "def_dpa_action"]
structure IsDpaAction (q' : L) (ρ : Dyck.Aq L q' →ₐ[L] Module.End L (Vstar L)) : Prop where
  /-- `ρ(𝟏_k)` is the projection of `V_*` onto its `k`-th summand `V_k`. -/
  map_e : ∀ k : ℕ, ρ (Dyck.Aq.e L q' k) = pieceProj L k

variable {ρ : Dyck.Aq L q' →ₐ[L] Module.End L (Vstar L)}

/-- **An action carries a path from `j` to `k` to an endomorphism vanishing on every summand but
`V_j` and mapping `V_j` into `V_k`**: the remark after `HJO.Sweep.IsDpaAction`, which it
justifies by `𝟏_kb𝟏_j = b` for such a path. Composing `ρ` with that identity and reading `ρ(𝟏_k)`
and `ρ(𝟏_j)` off the structure gives the displayed factorisation, whose two projections are exactly
the two statements of the remark. -/
theorem IsDpaAction.eq_pieceProj_mul_mul_pieceProj (h : IsDpaAction q' ρ) {j k : ℕ}
    {b : Dyck.Aq L q'} (hb : Dyck.Aq.e L q' k * b * Dyck.Aq.e L q' j = b) :
    ρ b = pieceProj L k * ρ b * pieceProj L j := by
  conv_lhs => rw [← hb]
  rw [map_mul, map_mul, h.map_e, h.map_e]

/-- **An action kills every summand but the source of the path**: for a path `b` from `j` to `k`,
the operator `ρ b` vanishes on `V_l` whenever `l ≠ j`. -/
theorem IsDpaAction.apply_ofPiece_of_ne (h : IsDpaAction q' ρ) {j k l : ℕ} (hl : l ≠ j)
    {b : Dyck.Aq L q'} (hb : Dyck.Aq.e L q' k * b * Dyck.Aq.e L q' j = b) (F : pieceSub L l) :
    ρ b (ofPiece L l F) = 0 := by
  rw [h.eq_pieceProj_mul_mul_pieceProj hb]
  change pieceProj L k (ρ b (pieceProj L j (ofPiece L l F))) = 0
  rw [pieceProj_ofPiece_of_ne hl, map_zero, map_zero]

end Action

end HJO.Sweep
