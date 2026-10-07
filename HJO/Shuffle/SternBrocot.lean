/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidData
public import HJO.Shuffle.Mellit
public meta import HJO.Attr

/-! # Stern–Brocot: every coprime slope is a mediant

`HJO.Sweep.exists_slopeActions` builds the action `ρ_{m,n}` attached to a coprime pair `(m, n)` by
strong induction on `m + n`, and the inductive step needs the pair to be the *mediant* of a
unimodular pair: `(m, n) = (m_1, n_1) + (m_2, n_2)` with `m_2n_1 - m_1n_2 = 1`. That is
`HJO.Mellit.exists_isUnimodular_add`, proved here.

## Main results

* `HJO.Mellit.exists_isUnimodular_add`.

## Implementation notes

The Bézout half of the proof is already proved: `HJO.Mellit.exists_isSBParent`, the
existence half of `HJO.Mellit.existsUnique_isSBParent`, produces the pair `(m_1, n_1)` with
`0 ≤ m_1 ≤ m`, `0 ≤ n_1 ≤ n` and `mn_1 - nm_1 = 1` — which is the `(b, a)` after its sign
correction, with the same normalisation `0 ≤ b ≤ m - 1` obtained by reducing modulo `m`. So all that
is left here is the *complement*: `(m_2, n_2) := (m - m_1, n - n_1)`, whose determinant against
`(m_1, n_1)` is `(m-m_1)n_1 - m_1(n-n_1) = mn_1 - nm_1 = 1`.

The two bounds `m_1 ≤ m` and `n_1 ≤ n` are what make the `ℕ` subtractions exact, and they are the
only use the proof makes of them; without them the complement would truncate and the determinant
identity would be false rather than unprovable.

The side condition `(m, n) ∉ {(0,1), (1,0)}` is spent on `1 ≤ m` and `1 ≤ n`, which is
what `exists_isSBParent` asks for: coprimality alone leaves `(0, 1)` and `(1, 0)`, and at those two
pairs no unimodular pair sums to them, both summands of a sum equal to `(0,1)` having first
coordinate `0` and hence determinant `0`.

## References

A. Mellit, *Toric braids and `(m, n)`-parking
functions*, §3.6.
-/

@[expose] public section

namespace HJO.Mellit

/-- **Stern–Brocot**, `HJO.Mellit.exists_isUnimodular_add`: a coprime pair `(m, n)` of naturals
other than `(0,1)` and `(1,0)` is the mediant of a unimodular pair.

The pair produced is `((m_1, n_1), (m - m_1, n - n_1))` with `(m_1, n_1)` the Stern–Brocot parent of
`HJO.Mellit.exists_isSBParent`; its determinant `(m-m_1)n_1 - m_1(n-n_1)` collapses to
`mn_1 - nm_1 = 1`. -/
@[hjo "lem_dpa_stern_brocot"]
theorem exists_isUnimodular_add {m n : ℕ} (hmn : Nat.Coprime m n) (h01 : (m, n) ≠ (0, 1))
    (h10 : (m, n) ≠ (1, 0)) :
    ∃ p p' : ℕ × ℕ, IsUnimodular p p' ∧ m = p.1 + p'.1 ∧ n = p.2 + p'.2 := by
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exact absurd (by rw [(Nat.coprime_zero_left n).mp hmn]) h01
    · exact h
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (by rw [(Nat.coprime_zero_right m).mp hmn]) h10
    · exact h
  obtain ⟨m₁, n₁, hm₁, hn₁, hdet⟩ := exists_isSBParent hmn hm hn
  have hkey : (m - m₁) * n₁ = m₁ * (n - n₁) + 1 := by
    zify [hm₁, hn₁]
    linear_combination hdet
  exact ⟨(m₁, n₁), (m - m₁, n - n₁), hkey, by omega, by omega⟩

end HJO.Mellit
