/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CornerCalculus
public meta import HJO.Attr

/-! # Powers of the corner elements, and the algebra at `q⁻¹`

Moving a loop past a *power* of a corner element leaves a sum of corrections, one for each way of
splitting the power; this file proves that, and the closed form of `y_1` as the commutator followed
by a descending word. It also names the algebra `𝔸_{q⁻¹}`, which is no new construction: the base
`q` of `HJO.Dyck.Aq` is an explicit argument, so `𝔸_{q⁻¹}` is that algebra at `⅟q`.

## Main definitions

* `HJO.Dyck.AqInv`: the algebra `𝔸_{q⁻¹}`.

## Main results

* `HJO.Dyck.Aq.yElt_one_eq_Delta`: `y_1 = q^{1-k}(q-1)^{-1}D_k(T_{k-1} ⋯ T_1)`.
* `HJO.Dyck.Aq.Tg_mul_yElt_pow`: `T_jy_{j+1}^c = y_j^cT_j + (q-1)∑_{s=1}^{c}y_j^sy_{j+1}^{c-s}`.

## Implementation notes

The power identity is proved once as `HJO.Dyck.pow_hecke_aux`, a statement about three elements of
an arbitrary ring satisfying `TZ = YT + (q-1)Y` and nothing else: the induction is the paper's, and
carrying `𝔸_q`'s idempotents and loop indices through it would add noise and no content. The
corner elements enter only when the abstract lemma is instantiated.

The sum is indexed by `Finset.range (c+1)` with the summand `y_j^{t+1}y_{j+1}^{c-t}`, which is the
sum `∑_{s=1}^{c+1}y_j^sy_{j+1}^{c+1-s}` at `s = t+1`; the hypothesis `c ≥ 1` is
carried by writing the exponent as `c + 1` rather than as a `1 ≤ c` side condition, so no truncated
subtraction of `ℕ` can be read at a value the statement does not intend. The exponent `c - t` is a
truncated subtraction, but only at `t ≤ c`, where it is exact.

`y_{j+1}^0` is the unit `1` of `𝔸_q` and not the idempotent `e_k`, which the empty
product would be. That costs nothing: the factor it multiplies is `y_j^{c+1}`, and `y_j` absorbs
`e_k` on the right, so the two readings of the last summand are the same element.

## References

The definition `HJO.Dyck.AqInv` and the lemmas `HJO.Dyck.Aq.yElt_one_eq_Delta` and
`HJO.Dyck.Aq.Tg_mul_yElt_pow`, on the Dyck path algebra, its involution, the double Dyck path
algebra and the slope actions; and E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*,
J. Amer. Math. Soc. **31** (2018) 661--697, Section 3.
-/

@[expose] public section

namespace HJO.Dyck

/-- **The algebra `𝔸_{q⁻¹}`**: the algebra of `HJO.Dyck.Aq` with `q` replaced throughout by `q⁻¹`.
This is not a second construction — `HJO.Dyck.Aq` takes its base `q` as an explicit argument
precisely so that the substituted algebra is an instance of it, and every theorem about `𝔸_q` is
therefore a theorem about `𝔸_{q⁻¹}` with no transport. -/
@[hjo "def_dpa_conj_algebra"]
abbrev AqInv (K : Type*) [CommRing K] (q : K) [Invertible q] : Type _ := Aq K ⅟q

/-- The quadratic relation of `𝔸_{q⁻¹}` is the paper's with `q` replaced by `q⁻¹`: the value check
that `HJO.Dyck.AqInv` is the substituted algebra and not the original one. -/
theorem AqInv.quadratic {K : Type*} [CommRing K] {q : K} [Invertible q] {k i : ℕ} (h : i + 2 ≤ k) :
    (Aq.Tg K ⅟q k i - Aq.e K ⅟q k) * (Aq.Tg K ⅟q k i + ⅟q • Aq.e K ⅟q k) = 0 :=
  Aq.quadratic h

/-! ### A loop past a power -/

/-- The paper's induction on the exponent, for three elements of an arbitrary ring related by
`TZ = YT + (q-1)Y`: each further factor of `Z` contributes one more summand. -/
theorem pow_hecke_aux {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A] {T Y Z : A}
    {q : K} (h : T * Z = Y * T + (q - 1) • Y) (c : ℕ) :
    T * Z ^ (c + 1)
      = Y ^ (c + 1) * T + (q - 1) • ∑ t ∈ Finset.range (c + 1), Y ^ (t + 1) * Z ^ (c - t) := by
  induction c with
  | zero => simpa using h
  | succ c ih =>
    have hsum : Y * (∑ t ∈ Finset.range (c + 1), Y ^ (t + 1) * Z ^ (c - t)) + Y * Z ^ (c + 1)
        = ∑ t ∈ Finset.range (c + 1 + 1), Y ^ (t + 1) * Z ^ (c + 1 - t) := by
      rw [Finset.sum_range_succ' (fun t => Y ^ (t + 1) * Z ^ (c + 1 - t)) (c + 1),
        Finset.mul_sum]
      simp only [Nat.succ_sub_succ, Nat.sub_zero, Nat.zero_add, pow_one, ← mul_assoc, ← pow_succ']
    calc T * Z ^ (c + 1 + 1)
        = T * Z * Z ^ (c + 1) := by rw [pow_succ', ← mul_assoc]
      _ = Y * (T * Z ^ (c + 1)) + (q - 1) • (Y * Z ^ (c + 1)) := by
          rw [h, add_mul, smul_mul_assoc, mul_assoc]
      _ = Y ^ (c + 1 + 1) * T
            + (q - 1) • (Y * (∑ t ∈ Finset.range (c + 1), Y ^ (t + 1) * Z ^ (c - t))
              + Y * Z ^ (c + 1)) := by
          rw [ih, mul_add, mul_smul_comm, ← mul_assoc, ← pow_succ', smul_add, add_assoc]
      _ = Y ^ (c + 1 + 1) * T
            + (q - 1) • ∑ t ∈ Finset.range (c + 1 + 1), Y ^ (t + 1) * Z ^ (c + 1 - t) := by
          rw [hsum]

namespace Aq

variable {K : Type*} [CommRing K] {q : K} [Invertible q] [Invertible (q - 1)]

/-- **A loop past a power of a corner element**:
`T_jy_{j+1}^c = y_j^cT_j + (q-1)∑_{s=1}^{c}y_j^sy_{j+1}^{c-s}`, the `c ≥ 1` being
carried by the exponent `c + 1`. -/
@[hjo "lem_cm_tj_ypower"]
theorem Tg_mul_yElt_pow {k j : ℕ} (h1 : 1 ≤ j) (hjk : j < k) (c : ℕ) :
    Tg K q k (j - 1) * yElt K q k (j + 1) ^ (c + 1)
      = yElt K q k j ^ (c + 1) * Tg K q k (j - 1)
        + (q - 1) • ∑ t ∈ Finset.range (c + 1),
            yElt K q k j ^ (t + 1) * yElt K q k (j + 1) ^ (c - t) :=
  pow_hecke_aux (Tg_mul_yElt_succ h1 hjk) c

/-! ### The commutator on the other side -/

/-- The defining formula for `y_k`, solved for the commutator on the left: the ascending word of
loops times the top corner element is `(q-1)^{-1}D_k`. -/
theorem tSegUp_mul_yElt_top {k : ℕ} (hk : 1 ≤ k) :
    tSegUp K q k 0 (k - 1) * yElt K q k k = ⅟(q - 1) • Delta K q (k - 1) := by
  rw [Delta_eq_smul_tSegUp_mul_yElt hk, smul_smul, invOf_mul_self, one_smul]

/-- **The closed form of `y_1` with the commutator in front**:
`y_1 = q^{1-k}(q-1)^{-1}D_k(T_{k-1} ⋯ T_1)`, the word being the idempotent when `k = 1`. The
ascending word of `HJO.Dyck.Aq.yElt_one_eq` cancels the descending word of inverses inside `y_k`,
leaving the commutator. -/
@[hjo "lem_cm_yelement_first"]
theorem yElt_one_eq_Delta {k : ℕ} (hk : 1 ≤ k) :
    yElt K q k 1
      = ((⅟q) ^ (k - 1) * ⅟(q - 1)) • (Delta K q (k - 1) * tSeg K q k 0 (k - 1)) := by
  rw [yElt_one_eq hk, tSegUp_mul_yElt_top hk, smul_mul_assoc, smul_smul]

end Aq

end HJO.Dyck
