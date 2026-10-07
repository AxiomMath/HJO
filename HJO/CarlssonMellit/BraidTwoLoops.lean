/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CornerPairs
public meta import HJO.Attr

/-! # The braid generator against a product of two loops, with the correction term

Mellit's §8.27 form of `HJO.Dyck.Aq.Tg_mul_yElt_pair`: the two Hecke moves
`T_iy_i = y_{i+1}T_i + (1-q)y_i` and `T_iy_{i+1} = y_iT_i + (q-1)y_i` combine into

`T_iy_iy_{i+1}𝟏_k = y_iy_{i+1}T_i𝟏_k + (y_{i+1}y_i - y_iy_{i+1})(T_i + (q-1)𝟏_k)`,

the correction term being the commutator of the two loops.

## Main results

* `HJO.Dyck.Aq.Tg_mul_yElt_pair_add_commutator`.

## Implementation notes

**The correction term is droppable.** One might argue that the term cannot be dropped from the
statement of `HJO.Dyck.Aq.Tg_mul_yElt_pair_add_commutator`, on the ground that at the vertex `2` the
commutation of `y_1` and `y_2` is left open by `HJO.Dyck.Aq.yElt_comm`. It is not open: the loop
commutation holds at every `k ≥ 1`, as `HJO.Dyck.Aq.yElt_comm` with hypotheses `1 ≤ i ≤ k` and
`1 ≤ j ≤ k` and nothing else. So `y_{i+1}y_i - y_iy_{i+1}` is `0` at every index the statement
admits, the correction term vanishes identically, and the statement is therefore *equivalent* to the
correction-free identity `HJO.Dyck.Aq.Tg_mul_yElt_pair` rather than weaker than it; this file states
it in its own shape.

The narrowing behind it is the same one recorded at `HJO.Dyck.Aq.yElt_comm`: Mellit's route
carries `T_1` down from the vertex `k` to `k-1` and so needs `1 ≤ k-2`, whereas the Carlsson--Mellit
route reads `T_id_- = d_-T_i` at the vertex `k+1` and needs only `1 ≤ k-1`. The vertex `2` falls to
the second route, and no injective raising operator is needed anywhere.

**The trailing `𝟏_k` is absorbed.** `HJO.Dyck.Aq.Tg_mul_e` and `HJO.Dyck.Aq.yElt_mul_e` make every
loop and every braid generator of the vertex `k` idempotent-absorbing on both sides, so writing
`T_i𝟏_k` for `T_i` would only restate the same element; the repo convention, recorded at
`HJO/Shuffle/DpaLoopsCommute.lean`, is to omit it. The `𝟏_k` inside `T_i + (q-1)𝟏_k` is *not*
absorbable and is kept: it is the unit of the corner algebra `𝟏_k𝔸_q𝟏_k`, which is not the unit of
`𝔸_q`.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, §8.27.
-/

@[expose] public section

namespace HJO.Dyck.Aq

variable {K : Type*} [CommRing K] {q : K} [Invertible q] [Invertible (q - 1)]

/-- **The braid generator against a product of two loops**:
`T_iy_iy_{i+1}𝟏_k = y_iy_{i+1}T_i𝟏_k + (y_{i+1}y_i - y_iy_{i+1})(T_i + (q-1)𝟏_k)` for `k ≥ 2` and
`1 ≤ i ≤ k-1`.

The correction term is identically `0`: `HJO.Dyck.Aq.yElt_comm` commutes the two loops at every
vertex `k ≥ 1`, so what is left is `HJO.Dyck.Aq.Tg_mul_yElt_pair`. See this file's implementation
notes for why the proof text says otherwise and why that remark is false. -/
@[hjo "lem_dpa_braid_two_loops"]
theorem Tg_mul_yElt_pair_add_commutator {k i : ℕ} (h1 : 1 ≤ i) (hik : i < k) :
    Tg K q k (i - 1) * (yElt K q k i * yElt K q k (i + 1))
      = yElt K q k i * yElt K q k (i + 1) * Tg K q k (i - 1)
        + (yElt K q k (i + 1) * yElt K q k i - yElt K q k i * yElt K q k (i + 1)) *
            (Tg K q k (i - 1) + (q - 1) • e K q k) := by
  rw [yElt_comm (i := i + 1) (j := i) (by omega) (by omega) (by omega) (by omega), sub_self,
    zero_mul, add_zero, Tg_mul_yElt_pair h1 hik]

end HJO.Dyck.Aq
