/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CornerCommute
public import HJO.Shuffle.DpaAction
public meta import HJO.Attr

/-! # The two lowest loops commute, in the algebra and in every action

At the vertex `2` the corner carries exactly two loops, `y_1` and `y_2`, and their commutation is
the one case of `y_iy_j = y_jy_i` that the route used at the higher vertices does not reach: that
route carries `T_1` down from the vertex `k` to `k-1` and needs `1 ≤ k-2`. The vertex-`2` case is
therefore usually given in weaker forms: `HJO.Dyck.Aq.dPlus_mul_yElt_low_commutator` asks only that
the raising generator kill the commutator, and `HJO.Sweep.map_yElt_low_comm` recovers the
commutation in an action from injectivity of the raising operator there.

**The vertex-`2` commutation is a theorem of `HJO.Dyck.Aq`.** `HJO.Dyck.Aq.yElt_comm` holds for
every `k ≥ 1` and all `1 ≤ i, j ≤ k`, with hypotheses `1 ≤ i ≤ k` and `1 ≤ j ≤ k` and nothing else,
and its proof — from `HJO.Dyck.Aq` alone, following Carlsson and Mellit — covers `k = 2`. The
Carlsson–Mellit route carries `T_1` up instead (`HJO.Dyck.Aq.Delta_mul_yElt_one`, stated for
`k ≥ 2`, whose `T_id_- = d_-T_i` is read at the vertex `k+1` and so needs only `1 ≤ k-1`), and that
settles `k = 2`. So the restriction to `k ≥ 3` is a limitation of one route and not a gap in the
mathematics.

So both results of this file are consequences of `HJO.Dyck.Aq.yElt_comm`, and the two hypotheses
usually attached to them — that the raising generator is applied at all, and that its image is
injective on `V_2` — are unnecessary. They are dropped, which only generalises the statements;
`HJO.Dyck.Aq.yElt_comm` implies each of the weaker forms immediately.

## Main results

* `HJO.Dyck.Aq.yElt_low_comm` — `y_1y_2 = y_2y_1` in `e_2𝔸_qe_2`, the vertex-`2` instance of
  `HJO.Dyck.Aq.yElt_comm`.
* `HJO.Dyck.Aq.dPlus_mul_yElt_low_commutator`.
* `HJO.Sweep.map_yElt_low_comm`.

## Implementation notes

The `𝟏_2` is not written, following the convention of
`HJO/CarlssonMellit/DpaMellitWords.lean`: `y_1` and `y_2` absorb the idempotent at the vertex
`2` on both sides (`HJO.Dyck.Aq.e_mul_yElt`, `HJO.Dyck.Aq.yElt_mul_e`), so a trailing `* e K q 2`
would only weaken the equation with `0`.

`HJO.Sweep.map_yElt_low_comm`'s "let `B` be `𝔸_q` or `𝔸_{q^{-1}}`" is one statement at a free base,
as in `HJO/Shuffle/DpaAction.lean`: `HJO.Dyck.AqInv K q` *is* `HJO.Dyck.Aq K ⅟q`
(`HJO.Dyck.AqInv`), so `q' = q` and `q' = ⅟q` are the two cases. The
`[Invertible (q' - 1)]` instance is not an added hypothesis but the condition under which
`HJO.Dyck.Aq.yElt` names anything at all, the loops carrying `(q-1)^{-1}`.

The conclusion is an equality of endomorphisms of the whole of `V_*`, which implies the stated
"on `V_2`". Nothing about the target is used beyond its being an algebra, and nothing about `ρ`
beyond its being a homomorphism: `HJO.Sweep.IsDpaAction`'s clause on the idempotents is not needed
either, so `HJO.Sweep.IsDpaAction` does not appear.

## References

Lemmas `HJO.Dyck.Aq.dPlus_mul_yElt_low_commutator` and `HJO.Sweep.map_yElt_low_comm`, using
`HJO.Dyck.Aq`, `HJO.Dyck.Aq.yElt`, `HJO.Dyck.AqInv` and `HJO.Sweep.IsDpaAction`; and
`HJO.Dyck.Aq.yElt_comm`. Consumed by `HJO.Sweep.exists_isDpaAction_replication`,
`HJO.Sweep.exists_isDpaAction_replication_star` and `HJO.Sweep.exists_slopeActions`. Transcribing
A. Mellit, *Toric braids and `(m, n)`-parking functions*, §3.2, and E. Carlsson and A. Mellit, *A
proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 3.
-/

@[expose] public section

namespace HJO.Dyck.Aq

variable {K : Type*} [CommRing K] {q : K} [Invertible q] [Invertible (q - 1)]

/-- **The two loops at the vertex `2` commute**: `y_1y_2 = y_2y_1` in `e_2𝔸_qe_2`. This is
`HJO.Dyck.Aq.yElt_comm` at `k = 2`, and it is the whole content of the two results below — it is a
theorem of the presentation, not a hypothesis on an action. -/
theorem yElt_low_comm : yElt K q 2 1 * yElt K q 2 2 = yElt K q 2 2 * yElt K q 2 1 :=
  yElt_comm (by omega) (by omega) (by omega) (by omega)

/-- **The raising generator kills the low commutator**, `HJO.Dyck.Aq.dPlus_mul_yElt_low_commutator`:
`d_+(y_1y_2 - y_2y_1)𝟏_2 = 0` in `𝔸_q`.

The commutator is itself `0` by `HJO.Dyck.Aq.yElt_low_comm`, so the factor `d_+` carries no weight;
the proof, which conjugates the two loops up to the vertex `3` by
`HJO.Dyck.Aq.dPlus_mul_yElt_words` and commutes them there, is a longer route to a weaker
statement. -/
@[hjo "lem_dpa_y_commute_low"]
theorem dPlus_mul_yElt_low_commutator :
    dPlus K q 2 * (yElt K q 2 1 * yElt K q 2 2 - yElt K q 2 2 * yElt K q 2 1) = 0 := by
  rw [yElt_low_comm, sub_self, mul_zero]

end HJO.Dyck.Aq

namespace HJO.Sweep

variable {L : Type*} [CommRing L] {q' : L} [Invertible q'] [Invertible (q' - 1)]

/-- **The loops commute in every action**, `HJO.Sweep.map_yElt_low_comm`: for `B`
either `𝔸_q` or `𝔸_{q^{-1}}` and `σ` an action of `B` on `V_*`, `σ(y_1y_2) = σ(y_2y_1)` on `V_2`.

The usual form asks in addition that `σ(d_+)` be injective on `V_2` and deduces the identity
from `HJO.Dyck.Aq.dPlus_mul_yElt_low_commutator`; neither is needed, `y_1y_2 = y_2y_1` holding in
`B` itself by `HJO.Dyck.Aq.yElt_low_comm`. So this is stated for an arbitrary `𝕜`-algebra
homomorphism out of `B`, which is strictly more than that form and is what
`HJO.Sweep.exists_slopeActions` consumes: its standing hypothesis "for every action `σ` …
`σ(y_1y_2) = σ(y_2y_1)` on `V_2`" is discharged outright. -/
@[hjo "lem_dpa_action_loops_commute"]
theorem map_yElt_low_comm (ρ : Dyck.Aq L q' →ₐ[L] Module.End L (Vstar L)) :
    ρ (Dyck.Aq.yElt L q' 2 1 * Dyck.Aq.yElt L q' 2 2)
      = ρ (Dyck.Aq.yElt L q' 2 2 * Dyck.Aq.yElt L q' 2 1) := by
  rw [Dyck.Aq.yElt_low_comm]

end HJO.Sweep
