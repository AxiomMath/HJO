/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.DpaReplicationPairs
public import HJO.Shuffle.SternBrocot
public meta import HJO.Attr

/-! # Mellit, the actions indexed by coprime pairs

`HJO.Sweep.exists_slopeActions`: from one correctly intertwined pair `(ρ^♭, ρ^{♭*})` the replication
of `HJO.Sweep.exists_isDpaAction_replication` and `HJO.Sweep.exists_isDpaAction_replication_star`
generates a family of actions `ρ_{m,n}` of `𝔸_q` and `ρ^*_{m,n}` of `𝔸_{q^{-1}}`, indexed by `ℕ²`,
such that every *unimodular* pair `((m_1,n_1),(m_2,n_2))` has `(ρ_{m_1,n_1}, ρ^*_{m_2,n_2})`
correctly intertwined and the two actions at the mediant `(m_1+m_2, n_1+n_2)` are the ones the two
replication lemmas produce from it.

## Main results

* `HJO.Sweep.exists_slopeActions`.
* `HJO.Mellit.IsUnimodular.descent` — every unimodular pair other than `((0,1),(1,0))` is a child of
  a unimodular pair of strictly smaller coordinate sum. This is the Stern–Brocot tree structure, and
  it is what the induction runs on.
* `HJO.Mellit.IsUnimodular.eq_of_isSplitting` — a pair of naturals has **at most one** unimodular
  splitting, which is what makes the recursion well defined.

## Implementation notes

**The family is indexed by all of `ℕ²`, not only by the coprime pairs.** Mellit attaches an
action to each coprime pair; a partial function is awkward to construct, so the recursion here is
total, returning `(ρ^♭, ρ^{♭*})` at every pair that is not a mediant of a unimodular pair. Nothing
is lost: the theorem's last clause feeds `HJO.Mellit.exists_isUnimodular_add` back in and says that
for a coprime `(m,n)` other than `(0,1)` and `(1,0)` the two actions attached to it *are*
replications of a unimodular pair, which is the reading. And `IsDpaAction` is asserted at every
index, which is stronger than at the coprime ones.

**The standing hypothesis is discharged, not carried.** The theorem assumes `σ(y_1y_2) = σ(y_2y_1)`
on `V_2` for every action `σ`; that is a theorem (`HJO.Dyck.Aq.yElt_comm`, holding in the algebra at
every vertex `k ≥ 1`), so neither `HJO.Sweep.exists_isDpaAction_replication` nor
`HJO.Sweep.exists_isDpaAction_replication_star` carries it and neither does
`HJO.Sweep.exists_slopeActions`. The observation that the hypothesis is available at the base pair
by `HJO.Sweep.map_yElt_low_comm`, both raising operators being injective on `V_2`, is therefore not
needed either.

**The base pair is a hypothesis rather than `HJO.Sweep.exists_isIntertwinedPair_vmod`.** The
natural starting point of the induction is `(ρ^♭, ρ^{♭*})` of `HJO.Sweep.exists_isDpaAction_mod` and
`HJO.Sweep.exists_isDpaAction_mellit`, correctly intertwined by
`HJO.Sweep.exists_isIntertwinedPair_vmod`. The theorem is stated over an arbitrary correctly
intertwined pair; that is a generalisation, and instantiating it at
`HJO.Sweep.exists_isIntertwinedPair_vmod` recovers the statement verbatim, with `R (0,1) = ρ^♭` and
`R' (1,0) = ρ^{♭*}`.

**The scalar `c` is a parameter, as at `HJO.Sweep.exists_isDpaAction_replication`.** The
`-(qu)^{-1}` is not expressible without `u` invertible; `HJO.Sweep.exists_isDpaAction_replication`
is proved for an arbitrary scalar, and the family here is built with one fixed `c` at every step, so
`c := -(⅟q * ⅟u)` recovers the construction with scalar `-(qu)^{-1}` wherever `u` is a unit.

**The recursion is on a fuel and not on well-founded recursion.** `HJO.Sweep.slopeAux` takes the
coordinate sum as a fuel and `HJO.Sweep.slopeAuxAgree` shows the value is independent of the fuel
once it is large enough; `HJO.Sweep.slopeFam` is the diagonal. The two unfolding lemmas
`HJO.Sweep.slopeFam_of_not_isSplitting` and `HJO.Sweep.slopeFam_mediant` are all the rest of the
library uses.

**Uniqueness of the splitting is the arithmetic content.**
`HJO.Mellit.IsUnimodular.eq_of_isSplitting` is the statement "if `((a,b),(c,d))` is
unimodular with `(a,b)+(c,d) = (m,n)` then `(a,b) = (m_1,n_1)`", proved here by
`m ∣ m_1 - m_1'` together with `m_1, m_1' < m`, rather than by "subtracting the two
relations", which on its own leaves the ambiguity by a multiple of `(m,n)`.

## References

This file proves `HJO.Sweep.exists_slopeActions`, using `HJO.Sweep.IsDpaAction`,
`HJO.Sweep.IsIntertwinedPair`, `HJO.Mellit.IsUnimodular`, `HJO.Sweep.exists_isDpaAction_mod`,
`HJO.Sweep.exists_isDpaAction_mellit`, `HJO.Sweep.exists_isIntertwinedPair_vmod`,
`HJO.Sweep.exists_isDpaAction_replication`, `HJO.Sweep.exists_isDpaAction_replication_star`,
`HJO.Sweep.isIntertwinedPair_replication_pairs` and `HJO.Mellit.exists_isUnimodular_add`. A. Mellit,
*Toric braids and `(m, n)`-parking functions*, §3.2.
-/

@[expose] public section

/-! ### The Stern–Brocot tree as a recursion principle on unimodular pairs -/

namespace HJO.Mellit

/-- **A unimodular pair is not the zero pair on either side.** `m'n = mn' + 1` fails at
`(m',n') = (0,0)` and at `(m,n) = (0,0)`, both sides of the equation then being `0` and `1`. -/
theorem IsUnimodular.right_pos {p p' : ℕ × ℕ} (h : IsUnimodular p p') : 1 ≤ p'.1 + p'.2 := by
  rcases Nat.eq_zero_or_pos (p'.1 + p'.2) with h0 | h0
  · exact absurd h (by
      have h1 : p'.1 = 0 := by omega
      have h2 : p'.2 = 0 := by omega
      simp only [IsUnimodular, h1, h2, Nat.zero_mul]
      omega)
  · exact h0

/-- **A unimodular pair is not the zero pair on either side**, the left-hand version. -/
theorem IsUnimodular.left_pos {p p' : ℕ × ℕ} (h : IsUnimodular p p') : 1 ≤ p.1 + p.2 := by
  rcases Nat.eq_zero_or_pos (p.1 + p.2) with h0 | h0
  · exact absurd h (by
      have h1 : p.1 = 0 := by omega
      have h2 : p.2 = 0 := by omega
      simp only [IsUnimodular, h1, h2, Nat.mul_zero]
      omega)
  · exact h0

/-- **The first coordinate of the left member of a unimodular pair is smaller than the mediant's.**
Were they equal the right member would have first coordinate `0`, and then `m'n = mn' + 1` reads
`0 = mn' + 1`. This bound is what pins the splitting down to one. -/
theorem IsUnimodular.fst_lt {p p' : ℕ × ℕ} (h : IsUnimodular p p') : p.1 < p.1 + p'.1 := by
  rcases Nat.eq_zero_or_pos p'.1 with h0 | h0
  · exact absurd h (by simp only [IsUnimodular, h0, Nat.zero_mul]; omega)
  · omega

/-- **The mediant identity**: `(m_1+m_2)n_1 = m_1(n_1+n_2) + 1` for a unimodular pair. Both
unimodularity and this identity say that the `2 × 2` determinant of the pair is `1`; this is the
form in which the left member is compared with the mediant, and the one the uniqueness argument
runs on. -/
theorem IsUnimodular.mediant_det {p p' : ℕ × ℕ} (h : IsUnimodular p p') :
    (p.1 + p'.1) * p.2 = p.1 * (p.2 + p'.2) + 1 := by
  rw [Nat.add_mul, h]; ring

/-- **Every unimodular pair other than `((0,1),(1,0))` has a componentwise comparison**, in the
numerical form the case split is made in. Either the right member is `≤` the left componentwise or
the left is `≤` the right; the mixed case `m_2 ≤ m_1`, `n_1 < n_2` contradicts
`m_2n_1 = m_1n_2 + 1`, and the mixed case `m_1 < m_2`, `n_2 < n_1` forces `m_2 + n_1 ≤ 2` and hence
the root. -/
theorem le_or_le_of_det {m₁ n₁ m₂ n₂ : ℕ} (h : m₂ * n₁ = m₁ * n₂ + 1)
    (hne : ¬(m₁ = 0 ∧ n₁ = 1 ∧ m₂ = 1 ∧ n₂ = 0)) :
    (m₂ ≤ m₁ ∧ n₂ ≤ n₁) ∨ (m₁ ≤ m₂ ∧ n₁ ≤ n₂) := by
  rcases le_or_gt m₂ m₁ with hm | hm
  · rcases le_or_gt n₂ n₁ with hn | hn
    · exact Or.inl ⟨hm, hn⟩
    · exact absurd h (by
        have : m₂ * n₁ ≤ m₁ * n₂ :=
          le_trans (Nat.mul_le_mul_right n₁ hm) (Nat.mul_le_mul_left m₁ hn.le)
        omega)
  · rcases le_or_gt n₁ n₂ with hn | hn
    · exact Or.inr ⟨hm.le, hn⟩
    · refine absurd ?_ hne
      obtain ⟨a, rfl⟩ : ∃ a, m₂ = a + 1 := ⟨m₂ - 1, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b, n₁ = b + 1 := ⟨n₁ - 1, by omega⟩
      have h1 : m₁ * n₂ ≤ a * b := Nat.mul_le_mul (by omega) (by omega)
      have h3 : (a + 1) * (b + 1) = a * b + a + b + 1 := by ring
      omega

/-- **Every unimodular pair other than `((0,1),(1,0))` has a componentwise comparison.** This is the
case split the descent runs on. -/
theorem IsUnimodular.le_or_le {p p' : ℕ × ℕ} (h : IsUnimodular p p')
    (hne : ¬(p = (0, 1) ∧ p' = (1, 0))) :
    (p'.1 ≤ p.1 ∧ p'.2 ≤ p.2) ∨ (p.1 ≤ p'.1 ∧ p.2 ≤ p'.2) := by
  obtain ⟨m₁, n₁⟩ := p
  obtain ⟨m₂, n₂⟩ := p'
  refine le_or_le_of_det h ?_
  rintro ⟨rfl, rfl, rfl, rfl⟩
  exact hne ⟨rfl, rfl⟩

/-- **The Stern–Brocot descent**: a unimodular pair other than the root `((0,1),(1,0))` is a child
of a unimodular pair, the parent being obtained by subtracting the smaller member from the larger.

Both branches keep the determinant, the subtraction only cancelling the cross term:
`m_2(n_1-n_2) - (m_1-m_2)n_2 = m_2n_1 - m_1n_2`. Together with
`HJO.Mellit.IsUnimodular.left_pos` and `.right_pos` — which say the subtracted member is not the
zero pair — this is the induction principle `HJO.Sweep.exists_slopeActions` runs on. -/
theorem IsUnimodular.descent {p p' : ℕ × ℕ} (h : IsUnimodular p p')
    (hne : ¬(p = (0, 1) ∧ p' = (1, 0))) :
    (∃ a : ℕ × ℕ, IsUnimodular a p' ∧ p.1 = a.1 + p'.1 ∧ p.2 = a.2 + p'.2) ∨
      (∃ b : ℕ × ℕ, IsUnimodular p b ∧ p'.1 = p.1 + b.1 ∧ p'.2 = p.2 + b.2) := by
  rcases h.le_or_le hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨(p.1 - p'.1, p.2 - p'.2), ?_, by omega, by omega⟩
    have : (p'.1 : ℤ) * (p.2 - p'.2) = ((p.1 : ℤ) - p'.1) * p'.2 + 1 := by
      have hz : (p'.1 : ℤ) * p.2 = (p.1 : ℤ) * p'.2 + 1 := by exact_mod_cast h
      linear_combination hz
    unfold IsUnimodular
    zify [h1, h2]
    exact this
  · refine Or.inr ⟨(p'.1 - p.1, p'.2 - p.2), ?_, by omega, by omega⟩
    have : ((p'.1 : ℤ) - p.1) * p.2 = (p.1 : ℤ) * ((p'.2 : ℤ) - p.2) + 1 := by
      have hz : (p'.1 : ℤ) * p.2 = (p.1 : ℤ) * p'.2 + 1 := by exact_mod_cast h
      linear_combination hz
    unfold IsUnimodular
    zify [h1, h2]
    exact this

/-- **`r` splits `p`**: `r` is a unimodular pair whose mediant is `p`. -/
def IsSplitting (p : ℕ × ℕ) (r : (ℕ × ℕ) × (ℕ × ℕ)) : Prop :=
  IsUnimodular r.1 r.2 ∧ p.1 = r.1.1 + r.2.1 ∧ p.2 = r.1.2 + r.2.2

instance (p : ℕ × ℕ) (r : (ℕ × ℕ) × (ℕ × ℕ)) : Decidable (IsSplitting p r) := by
  unfold IsSplitting; infer_instance

/-- **Each member of a splitting has strictly smaller coordinate sum than what it splits**, the
other member not being the zero pair. This is the measure the recursion decreases. -/
theorem IsSplitting.fst_lt {p : ℕ × ℕ} {r : (ℕ × ℕ) × (ℕ × ℕ)} (h : IsSplitting p r) :
    r.1.1 + r.1.2 < p.1 + p.2 := by
  obtain ⟨hu, hm, hn⟩ := h
  have := hu.right_pos
  omega

/-- **Each member of a splitting has strictly smaller coordinate sum than what it splits**, the
right-hand version. -/
theorem IsSplitting.snd_lt {p : ℕ × ℕ} {r : (ℕ × ℕ) × (ℕ × ℕ)} (h : IsSplitting p r) :
    r.2.1 + r.2.2 < p.1 + p.2 := by
  obtain ⟨hu, hm, hn⟩ := h
  have := hu.left_pos
  omega

/-- **A pair of naturals has at most one unimodular splitting**, the uniqueness claim
inside the proof of `HJO.Sweep.exists_slopeActions`.

Writing `m = m_1+m_2` and `n = n_1+n_2`, unimodularity is `mn_1 = m_1n + 1`, so two splittings
satisfy `m(n_1-n_1') = n(m_1-m_1')` in `ℤ`; multiplying `mn_1 - nm_1 = 1` by `m_1-m_1'` and
substituting turns that into `m_1-m_1' = m\big((m_1-m_1')n_1 - (n_1-n_1')m_1\big)`, so `m` divides
`m_1-m_1'`, which `HJO.Mellit.IsUnimodular.fst_lt` bounds strictly by `m` in absolute value. -/
theorem IsUnimodular.eq_of_isSplitting {p : ℕ × ℕ} {r r' : (ℕ × ℕ) × (ℕ × ℕ)}
    (h : IsSplitting p r) (h' : IsSplitting p r') : r = r' := by
  obtain ⟨hu, hm, hn⟩ := h
  obtain ⟨hu', hm', hn'⟩ := h'
  have hlt : r.1.1 < p.1 := hm ▸ hu.fst_lt
  have hlt' : r'.1.1 < p.1 := hm' ▸ hu'.fst_lt
  have e1 : (p.1 : ℤ) * r.1.2 = (r.1.1 : ℤ) * p.2 + 1 := by
    have := hu.mediant_det
    rw [hm, hn]; exact_mod_cast this
  have e2 : (p.1 : ℤ) * r'.1.2 = (r'.1.1 : ℤ) * p.2 + 1 := by
    have := hu'.mediant_det
    rw [hm', hn']; exact_mod_cast this
  have hz : (p.1 : ℤ) * ((r.1.2 : ℤ) - r'.1.2) = (p.2 : ℤ) * ((r.1.1 : ℤ) - r'.1.1) := by
    linear_combination e1 - e2
  have hdvd : (p.1 : ℤ) ∣ ((r.1.1 : ℤ) - r'.1.1) :=
    ⟨((r.1.1 : ℤ) - r'.1.1) * r.1.2 - ((r.1.2 : ℤ) - r'.1.2) * r.1.1, by
      linear_combination ((r'.1.1 : ℤ) - r.1.1) * e1 + (r.1.1 : ℤ) * hz⟩
  have hpos : (0 : ℤ) < (p.1 : ℤ) := by exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
  have hbd1 : -(p.1 : ℤ) < (r.1.1 : ℤ) - r'.1.1 := by omega
  have hbd2 : (r.1.1 : ℤ) - r'.1.1 < (p.1 : ℤ) := by omega
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : k = 0 := by
    rcases lt_trichotomy k 0 with h0 | h0 | h0
    · nlinarith [hbd1, hbd2]
    · exact h0
    · nlinarith [hbd1, hbd2]
  rw [hk0, mul_zero] at hk
  have hfst : r.1.1 = r'.1.1 := by omega
  have hsnd : r.1.2 = r'.1.2 := by
    have h0 : (p.1 : ℤ) * ((r.1.2 : ℤ) - r'.1.2) = 0 := by rw [hz, hfst]; ring
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 (by positivity)
    · have : (r.1.2 : ℤ) = r'.1.2 := by linarith
      exact_mod_cast this
  have : r.1 = r'.1 := Prod.ext hfst hsnd
  refine Prod.ext this (Prod.ext ?_ ?_) <;> omega

open scoped Classical in
/-- **The chosen unimodular splitting** of a pair of naturals, or `((0,0),(0,0))` when there is
none. By `HJO.Mellit.IsUnimodular.eq_of_isSplitting` the choice is no choice at all: whenever a
splitting exists this is *the* splitting. -/
noncomputable def sbSplit (p : ℕ × ℕ) : (ℕ × ℕ) × (ℕ × ℕ) :=
  if h : ∃ r, IsSplitting p r then h.choose else ((0, 0), (0, 0))

/-- **`sbSplit` splits whenever anything does.** -/
theorem isSplitting_sbSplit {p : ℕ × ℕ} (h : ∃ r, IsSplitting p r) : IsSplitting p (sbSplit p) := by
  classical
  rw [sbSplit, dite_eq_left h]
  exact h.choose_spec

/-- **`sbSplit` of a mediant is the unimodular pair it is the mediant of.** -/
theorem sbSplit_mediant {p p' : ℕ × ℕ} (h : IsUnimodular p p') :
    sbSplit (p.1 + p'.1, p.2 + p'.2) = (p, p') := by
  have hex : ∃ r, IsSplitting (p.1 + p'.1, p.2 + p'.2) r := ⟨(p, p'), h, rfl, rfl⟩
  exact IsUnimodular.eq_of_isSplitting (isSplitting_sbSplit hex) ⟨h, rfl, rfl⟩

/-- **`(0,1)` is not a mediant**: both members of a splitting would have first coordinate `0`, and
then the determinant is `0` rather than `1`. -/
theorem not_isSplitting_zero_one (r : (ℕ × ℕ) × (ℕ × ℕ)) : ¬IsSplitting (0, 1) r := by
  rintro ⟨hu, hm, -⟩
  simp only [IsUnimodular] at hu
  have h1 : r.1.1 = 0 := by omega
  have h2 : r.2.1 = 0 := by omega
  rw [h1, h2] at hu
  simp only [Nat.zero_mul] at hu
  omega

/-- **`(1,0)` is not a mediant**, the mirror of `HJO.Mellit.not_isSplitting_zero_one`. -/
theorem not_isSplitting_one_zero (r : (ℕ × ℕ) × (ℕ × ℕ)) : ¬IsSplitting (1, 0) r := by
  rintro ⟨hu, -, hn⟩
  simp only [IsUnimodular] at hu
  have h1 : r.1.2 = 0 := by omega
  have h2 : r.2.2 = 0 := by omega
  rw [h1, h2] at hu
  simp only [Nat.mul_zero] at hu
  omega

end HJO.Mellit

/-! ### The value clauses of the two replication lemmas -/

namespace HJO.Sweep

section Replicated

variable {L : Type*} [CommRing L] {q : L} [Invertible q] [Invertible (q - 1)]

/-- **`ρ_1` is the replication of `(σ, σ^*)` at the scalar `c`**, the conclusion of
`HJO.Sweep.exists_isDpaAction_replication` read as a property of `ρ_1` rather than as an existence:
`ρ_1` is an action of `𝔸_q` sharing the braid and lowering parts of `σ` and with
`ρ_1(d_+) = c·z_1d_+`. -/
structure IsReplicated (c : L) (σ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L))
    (σ' : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L))
    (ρ₁ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)) : Prop where
  /-- `ρ_1` is an action of `𝔸_q` on `V_*`. -/
  isAction : IsDpaAction q ρ₁
  /-- `ρ_1(T_i) = T_i`. -/
  map_Tg : ∀ k i : ℕ, ρ₁ (Dyck.Aq.Tg L q k i) = σ (Dyck.Aq.Tg L q k i)
  /-- `ρ_1(d_-) = d_-`. -/
  map_dMinus : ∀ k : ℕ, ρ₁ (Dyck.Aq.dMinus L q k) = σ (Dyck.Aq.dMinus L q k)
  /-- `ρ_1(d_+) = c·z_1d_+`. -/
  map_dPlus : ∀ k : ℕ, ρ₁ (Dyck.Aq.dPlus L q k)
    = c • (σ' (Dyck.Aq.yElt L ⅟q (k + 1) 1) * σ (Dyck.Aq.dPlus L q k))

/-- **`ρ_2` is the conjugate replication of `(σ, σ^*)`**, the conclusion of
`HJO.Sweep.exists_isDpaAction_replication_star` read as a property of `ρ_2`: an action of
`𝔸_{q^{-1}}` sharing the braid and lowering parts of `σ^*` and with `ρ_2(d_+) = -y_1d^*_+`. The
scalar is `-1` and is not free. -/
structure IsReplicatedStar (σ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L))
    (σ' : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L))
    (ρ₂ : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L)) : Prop where
  /-- `ρ_2` is an action of `𝔸_{q^{-1}}` on `V_*`. -/
  isAction : IsDpaAction ⅟q ρ₂
  /-- `ρ_2(T_i) = T_i^{-1}`, in the reading that `ρ_2` shares the braid part of `σ^*`. -/
  map_Tg : ∀ k i : ℕ, ρ₂ (Dyck.Aq.Tg L ⅟q k i) = σ' (Dyck.Aq.Tg L ⅟q k i)
  /-- `ρ_2(d_-) = d_-`. -/
  map_dMinus : ∀ k : ℕ, ρ₂ (Dyck.Aq.dMinus L ⅟q k) = σ' (Dyck.Aq.dMinus L ⅟q k)
  /-- `ρ_2(d_+) = -y_1d^*_+`. -/
  map_dPlus : ∀ k : ℕ, ρ₂ (Dyck.Aq.dPlus L ⅟q k)
    = (-1 : L) • (σ (Dyck.Aq.yElt L q (k + 1) 1) * σ' (Dyck.Aq.dPlus L ⅟q k))

variable {u : L} {σ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)}
  {σ' : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L)}

/-- **`HJO.Sweep.exists_isDpaAction_replication` in the packaged form**: a correctly intertwined
pair has a replication at every scalar. -/
theorem exists_isReplicated (h : IsIntertwinedPair q u σ σ') (c : L) :
    ∃ ρ₁, IsReplicated c σ σ' ρ₁ := by
  obtain ⟨ρ₁, hact, hT, hD, hU⟩ := exists_isDpaAction_replication h c
  exact ⟨ρ₁, hact, hT, hD, hU⟩

/-- **`HJO.Sweep.exists_isDpaAction_replication_star` in the packaged form.** That theorem states
`ρ_2(d_-) = d_-` against the *unstarred* `ρ`, the two agreeing by `HJO.Sweep.IsIntertwinedPair`'s
second condition; the form `HJO.Sweep.isIntertwinedPair_replication_pairs` consumes is the starred
one, so the two are composed here. -/
theorem exists_isReplicatedStar (h : IsIntertwinedPair q u σ σ') :
    ∃ ρ₂, IsReplicatedStar σ σ' ρ₂ := by
  obtain ⟨ρ₂, hact, hT, -, hD, hU⟩ := exists_isDpaAction_replication_star h
  exact ⟨ρ₂, hact, hT, fun k => (hD k).trans (h.map_dMinus_star k).symm, hU⟩

open scoped Classical in
/-- **The replication of `(σ, σ^*)` at the scalar `c`**, or `σ` when there is none. By
`HJO.Sweep.exists_isReplicated` there is one whenever the pair is correctly intertwined, which is
the only case the recursion reaches. -/
noncomputable def replOf (c : L) (σ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L))
    (σ' : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L)) :
    Dyck.Aq L q →ₐ[L] Module.End L (Vstar L) :=
  if h : ∃ ρ₁, IsReplicated c σ σ' ρ₁ then h.choose else σ

open scoped Classical in
/-- **The conjugate replication of `(σ, σ^*)`**, or `σ^*` when there is none. -/
noncomputable def replStarOf (σ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L))
    (σ' : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L)) :
    Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L) :=
  if h : ∃ ρ₂, IsReplicatedStar σ σ' ρ₂ then h.choose else σ'

/-- **`replOf` is the replication whenever one exists.** -/
theorem isReplicated_replOf {c : L} (h : ∃ ρ₁, IsReplicated c σ σ' ρ₁) :
    IsReplicated c σ σ' (replOf c σ σ') := by
  classical
  rw [replOf, dite_eq_left h]
  exact h.choose_spec

/-- **`replStarOf` is the conjugate replication whenever one exists.** -/
theorem isReplicatedStar_replStarOf (h : ∃ ρ₂, IsReplicatedStar σ σ' ρ₂) :
    IsReplicatedStar σ σ' (replStarOf σ σ') := by
  classical
  rw [replStarOf, dite_eq_left h]
  exact h.choose_spec

/-- **`replOf` is always an action**, being either a replication or `σ` itself. -/
theorem isDpaAction_replOf (c : L) (hσ : IsDpaAction q σ) : IsDpaAction q (replOf c σ σ') := by
  classical
  by_cases h : ∃ ρ₁, IsReplicated c σ σ' ρ₁
  · exact (isReplicated_replOf h).isAction
  · rw [replOf, dite_eq_right h]; exact hσ

/-- **`replStarOf` is always an action**, being either a conjugate replication or `σ^*` itself. -/
theorem isDpaAction_replStarOf (hσ' : IsDpaAction ⅟q σ') : IsDpaAction ⅟q (replStarOf σ σ') := by
  classical
  by_cases h : ∃ ρ₂, IsReplicatedStar σ σ' ρ₂
  · exact (isReplicatedStar_replStarOf h).isAction
  · rw [replStarOf, dite_eq_right h]; exact hσ'

end Replicated

/-! ### The family -/

section Family

variable {L : Type*} [CommRing L] {q u : L} [Invertible q] [Invertible (q - 1)]
  {ρb : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)}
  {ρb' : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L)}

/-- **The family of slope actions, with a fuel.** At a pair that is the mediant of a unimodular
pair the two actions are the replications of the actions attached to that pair; everywhere else
they are the two actions the recursion starts from. The fuel is the coordinate sum, and
`HJO.Sweep.slopeAuxAgree` shows the value does not depend on it once it is large enough. -/
noncomputable def slopeAux (c : L) (ρb : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L))
    (ρb' : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L)) :
    ℕ → ℕ × ℕ →
      (Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)) × (Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L))
  | 0, _ => (ρb, ρb')
  | N + 1, p =>
      if _ : Mellit.IsSplitting p (Mellit.sbSplit p) then
        (replOf c (slopeAux c ρb ρb' N (Mellit.sbSplit p).1).1
            (slopeAux c ρb ρb' N (Mellit.sbSplit p).2).2,
          replStarOf (slopeAux c ρb ρb' N (Mellit.sbSplit p).1).1
            (slopeAux c ρb ρb' N (Mellit.sbSplit p).2).2)
      else (ρb, ρb')

/-- **At a pair that is not a mediant the fuel is irrelevant.** -/
theorem slopeAux_of_not_isSplitting (c : L) (ρb : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L))
    (ρb' : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L)) {p : ℕ × ℕ}
    (h : ¬Mellit.IsSplitting p (Mellit.sbSplit p)) (N : ℕ) :
    slopeAux c ρb ρb' N p = (ρb, ρb') := by
  cases N with
  | zero => rfl
  | succ N => rw [slopeAux, dite_eq_right h]

/-- **The value does not depend on the fuel once it is at least the coordinate sum.** -/
theorem slopeAuxAgree (c : L) (ρb : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L))
    (ρb' : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L)) :
    ∀ N : ℕ, ∀ p : ℕ × ℕ, p.1 + p.2 ≤ N →
      slopeAux c ρb ρb' N p = slopeAux c ρb ρb' (p.1 + p.2) p := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro p hp
    by_cases hs : Mellit.IsSplitting p (Mellit.sbSplit p)
    · have h1 : (Mellit.sbSplit p).1.1 + (Mellit.sbSplit p).1.2 < p.1 + p.2 := hs.fst_lt
      have h2 : (Mellit.sbSplit p).2.1 + (Mellit.sbSplit p).2.2 < p.1 + p.2 := hs.snd_lt
      obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
      obtain ⟨S', hS'⟩ : ∃ S', p.1 + p.2 = S' + 1 := ⟨p.1 + p.2 - 1, by omega⟩
      have hA : slopeAux c ρb ρb' N' (Mellit.sbSplit p).1
          = slopeAux c ρb ρb' S' (Mellit.sbSplit p).1 := by
        rw [ih N' (by omega) _ (by omega), ih S' (by omega) _ (by omega)]
      have hB : slopeAux c ρb ρb' N' (Mellit.sbSplit p).2
          = slopeAux c ρb ρb' S' (Mellit.sbSplit p).2 := by
        rw [ih N' (by omega) _ (by omega), ih S' (by omega) _ (by omega)]
      rw [hS', slopeAux, slopeAux, dite_eq_left hs, dite_eq_left hs, hA, hB]
    · rw [slopeAux_of_not_isSplitting c ρb ρb' hs, slopeAux_of_not_isSplitting c ρb ρb' hs]

/-- **The family of slope actions**: the fuelled family read at its own coordinate sum. -/
noncomputable def slopeFam (c : L) (ρb : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L))
    (ρb' : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L)) (p : ℕ × ℕ) :
    (Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)) × (Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L)) :=
  slopeAux c ρb ρb' (p.1 + p.2) p

/-- **At a pair that is not a mediant the family is the pair it starts from.** -/
theorem slopeFam_of_not_isSplitting (c : L) (ρb : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L))
    (ρb' : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L)) {p : ℕ × ℕ}
    (h : ¬Mellit.IsSplitting p (Mellit.sbSplit p)) : slopeFam c ρb ρb' p = (ρb, ρb') :=
  slopeAux_of_not_isSplitting c ρb ρb' h _

/-- **At the mediant of a unimodular pair the family is the two replications** of the actions
attached to that pair. This is the only unfolding the rest of the library uses. -/
theorem slopeFam_mediant (c : L) (ρb : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L))
    (ρb' : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L)) {p p' : ℕ × ℕ}
    (h : Mellit.IsUnimodular p p') :
    slopeFam c ρb ρb' (p.1 + p'.1, p.2 + p'.2)
      = (replOf c (slopeFam c ρb ρb' p).1 (slopeFam c ρb ρb' p').2,
        replStarOf (slopeFam c ρb ρb' p).1 (slopeFam c ρb ρb' p').2) := by
  have hsp := Mellit.sbSplit_mediant h
  have hs : Mellit.IsSplitting (p.1 + p'.1, p.2 + p'.2)
      (Mellit.sbSplit (p.1 + p'.1, p.2 + p'.2)) := by rw [hsp]; exact ⟨h, rfl, rfl⟩
  have hlt1 : p.1 + p.2 < p.1 + p'.1 + (p.2 + p'.2) := by have := h.right_pos; omega
  have hlt2 : p'.1 + p'.2 < p.1 + p'.1 + (p.2 + p'.2) := by have := h.left_pos; omega
  obtain ⟨S', hS'⟩ : ∃ S', p.1 + p'.1 + (p.2 + p'.2) = S' + 1 :=
    ⟨p.1 + p'.1 + (p.2 + p'.2) - 1, by omega⟩
  unfold slopeFam
  simp only []
  rw [hS', slopeAux, dite_eq_left hs, hsp]
  rw [slopeAuxAgree c ρb ρb' S' p (by omega), slopeAuxAgree c ρb ρb' S' p' (by omega)]

variable (c : L)

/-- **Every member of the family is an action of `𝔸_q`**, `HJO.Sweep.replOf` being one whenever its
input is. -/
theorem isDpaAction_slopeFam (hb : IsDpaAction q ρb) :
    ∀ p : ℕ × ℕ, IsDpaAction q (slopeFam c ρb ρb' p).1 := by
  intro p
  induction hN : p.1 + p.2 using Nat.strong_induction_on generalizing p with
  | _ N ih =>
    by_cases hs : Mellit.IsSplitting p (Mellit.sbSplit p)
    · have hp : p = ((Mellit.sbSplit p).1.1 + (Mellit.sbSplit p).2.1,
          (Mellit.sbSplit p).1.2 + (Mellit.sbSplit p).2.2) := by
        rw [← hs.2.1, ← hs.2.2]
      rw [hp, slopeFam_mediant c ρb ρb' hs.1]
      refine isDpaAction_replOf c ?_
      exact ih ((Mellit.sbSplit p).1.1 + (Mellit.sbSplit p).1.2)
        (by rw [← hN]; exact hs.fst_lt) _ rfl
    · rw [slopeFam_of_not_isSplitting c ρb ρb' hs]; exact hb

/-- **Every member of the family is an action of `𝔸_{q^{-1}}`.** -/
theorem isDpaAction_slopeFam_star (hb' : IsDpaAction ⅟q ρb') :
    ∀ p : ℕ × ℕ, IsDpaAction ⅟q (slopeFam c ρb ρb' p).2 := by
  intro p
  induction hN : p.1 + p.2 using Nat.strong_induction_on generalizing p with
  | _ N ih =>
    by_cases hs : Mellit.IsSplitting p (Mellit.sbSplit p)
    · have hp : p = ((Mellit.sbSplit p).1.1 + (Mellit.sbSplit p).2.1,
          (Mellit.sbSplit p).1.2 + (Mellit.sbSplit p).2.2) := by
        rw [← hs.2.1, ← hs.2.2]
      rw [hp, slopeFam_mediant c ρb ρb' hs.1]
      refine isDpaAction_replStarOf ?_
      exact ih ((Mellit.sbSplit p).2.1 + (Mellit.sbSplit p).2.2)
        (by rw [← hN]; exact hs.snd_lt) _ rfl
    · rw [slopeFam_of_not_isSplitting c ρb ρb' hs]; exact hb'

/-- **Every unimodular pair is correctly intertwined by the family**, the induction of
`HJO.Sweep.exists_slopeActions`.

Strong induction on the total coordinate sum along the Stern–Brocot descent of
`HJO.Mellit.IsUnimodular.descent`: at the root the two actions are the ones the family starts from,
and a child is intertwined by `HJO.Sweep.isIntertwinedPair_replication_pairs` — by
`HJO.Sweep.isIntertwinedPair_replication` when the left member grew and by
`HJO.Sweep.isIntertwinedPair_replicationStar` when the right one did. -/
theorem isIntertwinedPair_slopeFam (h : IsIntertwinedPair q u ρb ρb') :
    ∀ p p' : ℕ × ℕ, Mellit.IsUnimodular p p' →
      IsIntertwinedPair q u (slopeFam c ρb ρb' p).1 (slopeFam c ρb ρb' p').2 := by
  intro p p'
  induction hN : p.1 + p.2 + p'.1 + p'.2 using Nat.strong_induction_on generalizing p p' with
  | _ N ih =>
    intro hu
    by_cases hroot : p = (0, 1) ∧ p' = (1, 0)
    · obtain ⟨rfl, rfl⟩ := hroot
      rw [slopeFam_of_not_isSplitting c ρb ρb' (Mellit.not_isSplitting_zero_one _),
        slopeFam_of_not_isSplitting c ρb ρb' (Mellit.not_isSplitting_one_zero _)]
      exact h
    · rcases hu.descent hroot with ⟨a, ha, hm, hn⟩ | ⟨b, hb, hm, hn⟩
      · have hprev : IsIntertwinedPair q u (slopeFam c ρb ρb' a).1 (slopeFam c ρb ρb' p').2 :=
          ih (a.1 + a.2 + p'.1 + p'.2) (by rw [← hN]; have := ha.right_pos; omega) a p' rfl ha
        have hp : p = (a.1 + p'.1, a.2 + p'.2) := by rw [← hm, ← hn]
        have hrep := isReplicated_replOf (exists_isReplicated hprev c)
        have hrepS := isReplicatedStar_replStarOf (exists_isReplicatedStar hprev)
        rw [hp, slopeFam_mediant c ρb ρb' ha]
        exact isIntertwinedPair_replication hprev c hrep.isAction hrep.map_Tg hrep.map_dMinus
          hrep.map_dPlus
      · have hprev : IsIntertwinedPair q u (slopeFam c ρb ρb' p).1 (slopeFam c ρb ρb' b).2 :=
          ih (p.1 + p.2 + b.1 + b.2) (by rw [← hN]; have := hb.left_pos; omega) p b rfl hb
        have hp' : p' = (p.1 + b.1, p.2 + b.2) := by rw [← hm, ← hn]
        have hrepS := isReplicatedStar_replStarOf (exists_isReplicatedStar hprev)
        rw [hp', slopeFam_mediant c ρb ρb' hb]
        exact isIntertwinedPair_replicationStar hprev hrepS.isAction hrepS.map_Tg
          hrepS.map_dMinus hrepS.map_dPlus

end Family

/-! ### The main theorem -/

section Node

variable {L : Type*} [CommRing L] {q u : L} [Invertible q] [Invertible (q - 1)]
  {ρb : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)}
  {ρb' : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L)}

/-- **Mellit, the actions indexed by coprime pairs**, `HJO.Sweep.exists_slopeActions`: from
a correctly intertwined pair `(ρ^♭, ρ^{♭*})` there is a family `ρ_{m,n}` of actions of `𝔸_q` and a
family `ρ^*_{m,n}` of actions of `𝔸_{q^{-1}}` on `V_*` with `ρ_{0,1} = ρ^♭`, `ρ^*_{1,0} = ρ^{♭*}`,
such that for every unimodular pair `((m_1,n_1),(m_2,n_2))` the pair
`(ρ_{m_1,n_1}, ρ^*_{m_2,n_2})` is correctly intertwined and the two actions attached to the mediant
`(m_1+m_2, n_1+n_2)` are the ones produced from it by `HJO.Sweep.exists_isDpaAction_replication` and
`HJO.Sweep.exists_isDpaAction_replication_star`.

The last clause closes the loop with `HJO.Mellit.exists_isUnimodular_add`: every coprime `(m,n)`
other than the two axis pairs *is* such a mediant, so the two actions attached to it are
replications. The family is defined at every pair of naturals rather than only at the coprime ones,
which is why the construction needs no partial function; at a pair that is not a mediant it returns
the two actions it starts from.

Three departures from the most direct formulation, all recorded in this file's implementation
notes: the base pair is a hypothesis rather than `HJO.Sweep.exists_isIntertwinedPair_vmod`; the
scalar `c` of `HJO.Sweep.exists_isDpaAction_replication` is a parameter, the
`-(qu)^{-1}` not being expressible without `u` invertible; and the standing hypothesis
`σ(y_1y_2) = σ(y_2y_1)` on `V_2` is discharged (`HJO.Dyck.Aq.yElt_comm`) and not carried. -/
@[hjo "thm_dpa_slope_actions"]
theorem exists_slopeActions (h : IsIntertwinedPair q u ρb ρb') (c : L) :
    ∃ (R : ℕ × ℕ → (Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)))
      (R' : ℕ × ℕ → (Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L))),
      R (0, 1) = ρb ∧ R' (0, 1) = ρb' ∧ R (1, 0) = ρb ∧ R' (1, 0) = ρb'
      ∧ (∀ p : ℕ × ℕ, IsDpaAction q (R p))
      ∧ (∀ p : ℕ × ℕ, IsDpaAction ⅟q (R' p))
      ∧ (∀ p p' : ℕ × ℕ, Mellit.IsUnimodular p p' →
          IsIntertwinedPair q u (R p) (R' p')
            ∧ IsReplicated c (R p) (R' p') (R (p.1 + p'.1, p.2 + p'.2))
            ∧ IsReplicatedStar (R p) (R' p') (R' (p.1 + p'.1, p.2 + p'.2)))
      ∧ (∀ m n : ℕ, Nat.Coprime m n → (m, n) ≠ (0, 1) → (m, n) ≠ (1, 0) →
          ∃ p p' : ℕ × ℕ, Mellit.IsUnimodular p p' ∧ m = p.1 + p'.1 ∧ n = p.2 + p'.2
            ∧ IsIntertwinedPair q u (R p) (R' p')
            ∧ IsReplicated c (R p) (R' p') (R (m, n))
            ∧ IsReplicatedStar (R p) (R' p') (R' (m, n))) := by
  classical
  have hb1 : (slopeFam c ρb ρb' (0, 1)).1 = ρb := by
    rw [slopeFam_of_not_isSplitting c ρb ρb' (Mellit.not_isSplitting_zero_one _)]
  have hb2 : (slopeFam c ρb ρb' (0, 1)).2 = ρb' := by
    rw [slopeFam_of_not_isSplitting c ρb ρb' (Mellit.not_isSplitting_zero_one _)]
  have hb3 : (slopeFam c ρb ρb' (1, 0)).1 = ρb := by
    rw [slopeFam_of_not_isSplitting c ρb ρb' (Mellit.not_isSplitting_one_zero _)]
  have hb4 : (slopeFam c ρb ρb' (1, 0)).2 = ρb' := by
    rw [slopeFam_of_not_isSplitting c ρb ρb' (Mellit.not_isSplitting_one_zero _)]
  have hmain : ∀ p p' : ℕ × ℕ, Mellit.IsUnimodular p p' →
      IsIntertwinedPair q u (slopeFam c ρb ρb' p).1 (slopeFam c ρb ρb' p').2
        ∧ IsReplicated c (slopeFam c ρb ρb' p).1 (slopeFam c ρb ρb' p').2
            (slopeFam c ρb ρb' (p.1 + p'.1, p.2 + p'.2)).1
        ∧ IsReplicatedStar (slopeFam c ρb ρb' p).1 (slopeFam c ρb ρb' p').2
            (slopeFam c ρb ρb' (p.1 + p'.1, p.2 + p'.2)).2 := by
    intro p p' hu
    have hpair := isIntertwinedPair_slopeFam c h p p' hu
    refine ⟨hpair, ?_, ?_⟩
    · rw [slopeFam_mediant c ρb ρb' hu]
      exact isReplicated_replOf (exists_isReplicated hpair c)
    · rw [slopeFam_mediant c ρb ρb' hu]
      exact isReplicatedStar_replStarOf (exists_isReplicatedStar hpair)
  refine ⟨fun p => (slopeFam c ρb ρb' p).1, fun p => (slopeFam c ρb ρb' p).2, hb1, hb2, hb3, hb4,
    isDpaAction_slopeFam c h.isAction, isDpaAction_slopeFam_star c h.isActionStar, hmain, ?_⟩
  intro m n hmn h01 h10
  obtain ⟨p, p', hu, hm, hn⟩ := Mellit.exists_isUnimodular_add hmn h01 h10
  obtain ⟨hpair, hrep, hrepS⟩ := hmain p p' hu
  have hmn' : ((m, n) : ℕ × ℕ) = (p.1 + p'.1, p.2 + p'.2) := by rw [hm, hn]
  refine ⟨p, p', hu, hm, hn, hpair, ?_, ?_⟩
  · rw [hmn']; exact hrep
  · rw [hmn']; exact hrepS

end Node

end HJO.Sweep

end
