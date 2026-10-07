/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.ShuffleClosed
public import QSeriesLib.NumberTheory.HJO.Basic
public meta import HJO.Attr

/-! # The main theorems

The finite identity `F_N(q) = (q)_N C_{𝐜,≤N}(q)` for coprime `1 < a < b`, and the
Huang--Jiang--Oblomkov conjecture `Z_{a,b}(q) = P_{a,b}(q)` for every coprime pair, both with no
hypothesis. Every result from the literature that the proof uses is proved in this library: the
collinear commutativity of the slope operators is `HJO.Debt.collinearCommutation`, the
compositional rational shuffle identity is `HJO.Ascent.shuffle`, and the six others are in
`HJO/Discharged/`.

## Main results

* `HJO.finiteSeries_eq_qPochhammer_mul_boundedGF`: the finite identity, restated as
  `HJO.Challenge.thm_finite`.
* `HJO.conjecture`: the conjecture at every coprime pair `a, b`, restated as
  `HJO.Challenge.thm_main`.

## Implementation notes

The library proves the conjecture under the standing convention `1 < a < b`
(`HJO.conjecture_of_one_lt_of_lt`). The remaining coprime pairs follow from the two facts of
`QSeriesLib`: both sides of the conjecture are symmetric in `a` and `b` (`HJO.comm`),
and at `a = 1` the gap set is empty and the conjecture is `1 = 1` (`HJO.one_left`).
-/

@[expose] public section

namespace HJO

open HJO.PhiMul.Witness (Base)

/-- **The finite identity `F_N(q) = (q)_N C_{𝐜,≤N}(q)`.** For coprime `1 < a < b` and every rank
`N`, the HJO polynomial is `(q)_N` times the volume generating function of the balanced cylindric
partitions with every entry at most `N`. -/
@[hjo "thm_finite"]
theorem finiteSeries_eq_qPochhammer_mul_boundedGF {a b : ℕ} (hab : Nat.Coprime a b) (ha : 1 < a)
    (hb : a < b) (N : ℕ) :
    Gaps.finiteSeries a b N
      = qPochhammer PowerSeries.X PowerSeries.X N * Cylindric.boundedGF a b N :=
  Debt.finiteSeries_eq_of_shuffle (Ascent.shuffle Base) hab ha hb N

/-- The Huang--Jiang--Oblomkov conjecture under the standing convention `1 < a < b`. -/
theorem conjecture_of_one_lt_of_lt {a b : ℕ} (hab : Nat.Coprime a b) (ha : 1 < a) (hb : a < b) :
    Conjecture a b :=
  Debt.conjecture_of_shuffle (Ascent.shuffle Base) hab ha hb

/-- The Huang--Jiang--Oblomkov conjecture for coprime `a ≤ b`. At `a = 0` coprimality forces
`b = 1`, at `a = 1` it is `HJO.one_left`, and `a = b` forces `a = b = 1`. -/
theorem conjecture_of_le {a b : ℕ} (hab : Nat.Coprime a b) (hle : a ≤ b) : Conjecture a b := by
  rcases Nat.lt_or_ge 1 a with ha | ha
  · rcases hle.lt_or_eq with hlt | rfl
    · exact conjecture_of_one_lt_of_lt hab ha hlt
    · rw [Nat.coprime_self] at hab
      omega
  · interval_cases a
    · rw [Nat.coprime_zero_left] at hab
      subst hab
      exact (comm 0 1).2 (one_left 0)
    · exact one_left b

/-- **The Huang--Jiang--Oblomkov conjecture.** For every coprime pair `a, b`, the HJO series
`Z_{a,b}(q)` equals the HJO product `P_{a,b}(q)`. -/
@[hjo "thm_main"]
theorem conjecture {a b : ℕ} (hab : Nat.Coprime a b) : Conjecture a b := by
  rcases le_total a b with hle | hle
  · exact conjecture_of_le hab hle
  · exact (comm a b).2 (conjecture_of_le hab.symm hle)

end HJO
