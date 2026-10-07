/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidTrainGen
public meta import HJO.Attr

/-! # Collision: an ascending train against a descending one

`HJO.Braid.IsBraidSystem.collide` is the one identity Mellit's Section 5 computes with:
`T_{a↗b} T_{c↘d} = T_{c'↘d'} T_{a'↗b'}`, where `(a',b',c',d')` are the collision indices of
`HJO.Braid.collideIndex`. This file proves it, in the two halves: the one-letter case
`HJO.Braid.IsBraidSystem.collide_base`, which is the four rules of `HJO/Shuffle/BraidTrainGen.lean`
plus far commutation and gluing, sorted by where the letter sits relative to the train's range; and
then the induction on `|a - b|` that peels one letter off the ascending train at a time.

## Main results

* `HJO.Braid.IsBraidSystem.collide_base`.
* `HJO.Braid.IsBraidSystem.collide`.
* `HJO.Braid.exists_nat_indexShift`, `HJO.Braid.exists_nat_collideIndex` — the collision indices of
  a quadruple in `[1, k]` are again a quadruple of naturals in `[1, k]`. This is what the induction
  needs in order to apply itself to the shortened train, and it is stated here because it is a fact
  about `HJO.Braid.indexShift` and nothing else.

## Implementation notes

### The collision indices are integers and the trains are indexed by naturals

`HJO.Braid.indexShift` and `HJO.Braid.collideIndex` are over `ℤ`, as they are usually stated,
while `HJO.Braid.trainUp` and `HJO.Braid.trainDown` read `ℕ`. The statements below therefore take
the output indices as four *naturals* together with the hypothesis that they are the collision
indices, `collideIndex a b c d = (a', b', c', d')` read in `ℤ`.

That hypothesis is not vacuous, and `HJO.Braid.exists_nat_collideIndex` is the proof: every shift
of `HJO.Braid.indexShift` maps `[1, k]` into `[1, k]` — its four clauses return `p`, `x + 1` only
when `x < q ≤ k`, `x - 1` only when `x > q ≥ 1`, or `x` — so the collision indices of a quadruple in
`[1, k]` are again one. The induction of `HJO.Braid.IsBraidSystem.collide` needs that existence to
apply its own hypothesis to the shortened train, so the lemma is not decoration.

### Which case is which

The four cases of `HJO.Braid.IsBraidSystem.collide_base` are sorted by the position of
`j = min(a,b)` relative to the range `[m, M] = [min(c,d), max(c,d) - 1]` of the train's letters.
Here Case 1 — the letter is far from every letter of the train — is taken first and for both signs
of the train at once, because the condition `max(a,b) + 1 ≤ min(c,d) ∨ max(c,d) + 1 ≤ min(a,b)` and
the conclusion `(a',b',c',d') = (a,b,c,d)` do not depend on which of `c`, `d` is the larger. The
other two live cases are then split by the sign of the train, `d < c` calling
`HJO.Braid.IsBraidSystem.gen_shift_pos`/`HJO.Braid.IsBraidSystem.gen_split_pos` and `c < d` calling
the two negative rules. The cases `j = c - 1` and `j = c` (for `d < c`) and `j = c - 1` (for
`c < d`) are the impossible positions: each forces `a = c` or `b = c`, and both are excluded.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*,
Section 5.
-/

@[expose] public section

namespace HJO.Braid

/-! ### The collision indices of a quadruple in range are a quadruple in range -/

/-- **The shift of `HJO.Braid.indexShift` maps `[1, K]` into `[1, K]`**: its four clauses return
`p`, or `x + 1` when `x < q`, or `x - 1` when `x > q`, or `x`, and each stays inside the interval.
The value is exhibited as a natural number, which is what the trains of `HJO.Braid.trainUp` and
`HJO.Braid.trainDown` read. -/
theorem exists_nat_indexShift {p q x : ℤ} {K : ℕ} (hp : 1 ≤ p) (hpK : p ≤ K) (hq : 1 ≤ q)
    (hqK : q ≤ K) (hx : 1 ≤ x) (hxK : x ≤ K) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ K ∧ (n : ℤ) = indexShift p q x := by
  refine ⟨(indexShift p q x).toNat, ?_, ?_, ?_⟩ <;> unfold indexShift <;> split_ifs <;> omega

/-- **The collision indices of `HJO.Braid.collideIndex` of a quadruple in `[1, k]` are again a
quadruple of naturals in `[1, k]`**, by `HJO.Braid.exists_nat_indexShift` four times. This is what
lets the induction of `HJO.Braid.IsBraidSystem.collide` apply itself to the shortened train. -/
theorem exists_nat_collideIndex {k a b c d : ℕ} (ha : 1 ≤ a) (hak : a ≤ k) (hb : 1 ≤ b)
    (hbk : b ≤ k) (hc : 1 ≤ c) (hck : c ≤ k) (hd : 1 ≤ d) (hdk : d ≤ k) :
    ∃ a' b' c' d' : ℕ, (1 ≤ a' ∧ a' ≤ k) ∧ (1 ≤ b' ∧ b' ≤ k) ∧ (1 ≤ c' ∧ c' ≤ k) ∧
      (1 ≤ d' ∧ d' ≤ k) ∧
      collideIndex (a : ℤ) (b : ℤ) (c : ℤ) (d : ℤ) = ((a' : ℤ), (b' : ℤ), (c' : ℤ), (d' : ℤ)) := by
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hak' : (a : ℤ) ≤ k := by exact_mod_cast hak
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hbk' : (b : ℤ) ≤ k := by exact_mod_cast hbk
  have hc' : (1 : ℤ) ≤ c := by exact_mod_cast hc
  have hck' : (c : ℤ) ≤ k := by exact_mod_cast hck
  have hd' : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have hdk' : (d : ℤ) ≤ k := by exact_mod_cast hdk
  obtain ⟨C, hC1, hCk, hCeq⟩ := exists_nat_indexShift (K := k) ha' hak' hb' hbk' hc' hck'
  have hC1' : (1 : ℤ) ≤ C := by exact_mod_cast hC1
  have hCk' : (C : ℤ) ≤ k := by exact_mod_cast hCk
  obtain ⟨B, hB1, hBk, hBeq⟩ := exists_nat_indexShift (K := k) hd' hdk' hc' hck' hb' hbk'
  have hB1' : (1 : ℤ) ≤ B := by exact_mod_cast hB1
  have hBk' : (B : ℤ) ≤ k := by exact_mod_cast hBk
  obtain ⟨A, hA1, hAk, hAeq⟩ := exists_nat_indexShift (K := k) hd' hdk' hC1' hCk' ha' hak'
  have hA1' : (1 : ℤ) ≤ A := by exact_mod_cast hA1
  have hAk' : (A : ℤ) ≤ k := by exact_mod_cast hAk
  obtain ⟨D, hD1, hDk, hDeq⟩ := exists_nat_indexShift (K := k) hA1' hAk' hB1' hBk' hd' hdk'
  refine ⟨A, B, C, D, ⟨hA1, hAk⟩, ⟨hB1, hBk⟩, ⟨hC1, hCk⟩, ⟨hD1, hDk⟩, ?_⟩
  rw [collideIndex_eq, ← hCeq, ← hBeq, ← hAeq, ← hDeq]

variable {M : Type*} [Monoid M] {k : ℕ} {T Tinv : ℕ → M}

/-! ### One letter against a descending train -/

/-- **Collision, one letter against a descending train**, that is
`HJO.Braid.IsBraidSystem.collide_base`: for `|a - b| = 1` and `b ≠ c`,
`T_{a↗b} T_{c↘d} = T_{c'↘d'} T_{a'↗b'}` with `(a',b',c',d')` the collision indices.

The case division is sorted by where `min(a,b)` sits relative to the range of the
train's letters: the letter commutes with the whole train (`HJO.Braid.trainDown_far_comm`), or its
index shifts by one (`HJO.Braid.IsBraidSystem.gen_shift_pos`,
`HJO.Braid.IsBraidSystem.gen_shift_neg`), or it lengthens the train and leaves a two-letter
ascending train behind (`HJO.Braid.IsBraidSystem.gen_split_pos`,
`HJO.Braid.IsBraidSystem.gen_split_neg`), or it starts at the train's head and glues onto it
(`HJO.Braid.trainUp_eq_trainDown_of_adjacent`, `HJO.Braid.trainDown_mul_trainDown`). -/
@[hjo "lem_train_collide_base"]
theorem IsBraidSystem.collide_base (h : IsBraidSystem k T Tinv) {a b c d a' b' c' d' : ℕ}
    (ha : 1 ≤ a) (hak : a ≤ k) (hb : 1 ≤ b) (hbk : b ≤ k) (hc : 1 ≤ c) (hck : c ≤ k)
    (hd : 1 ≤ d) (hdk : d ≤ k) (hab : a = b + 1 ∨ b = a + 1) (hbc : b ≠ c)
    (hcol : collideIndex (a : ℤ) (b : ℤ) (c : ℤ) (d : ℤ)
      = ((a' : ℤ), (b' : ℤ), (c' : ℤ), (d' : ℤ))) :
    trainUp T Tinv a b * trainDown T Tinv c d
      = trainDown T Tinv c' d' * trainUp T Tinv a' b' := by
  rw [collideIndex_eq] at hcol
  simp only [Prod.mk.injEq] at hcol
  obtain ⟨hA, hB, hC, hD⟩ := hcol
  rw [hC] at hA
  rw [hC, hA, hB] at hD
  by_cases hac : a = c
  · -- Case 3: the letter starts at the head of the train and glues onto it.
    have hba : b = c + 1 ∨ c = b + 1 := by omega
    have habs : |(b : ℤ) - (c : ℤ)| = 1 := by
      rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]; omega
    have ec : c' = b := by unfold indexShift at hC; split_ifs at hC <;> omega
    have hb'd : (b' : ℤ) ≠ (d : ℤ) := by
      rw [← hB]; exact indexShift_ne_head (by exact_mod_cast hbc)
    have hsame : indexShift (d : ℤ) (c : ℤ) (b : ℤ) = (a' : ℤ) := by
      rw [← indexShift_comm_adjacent habs, ← hA, ec, hac]
    have ea : a' = b' := by omega
    have ed : d' = d := by unfold indexShift at hD; split_ifs at hD <;> omega
    rw [ec, ed, ea, trainUp_self, mul_one, hac, trainUp_eq_trainDown_of_adjacent T Tinv hba]
    exact trainDown_mul_trainDown h hb hbk hc hck hd hdk
  by_cases hcd : c = d
  · -- The train is empty, and so is the one on the other side.
    have ec : c' = c := by unfold indexShift at hC; split_ifs at hC <;> omega
    have eb : b' = b := by unfold indexShift at hB; split_ifs at hB <;> omega
    have ea : a' = a := by unfold indexShift at hA; split_ifs at hA <;> omega
    have ed : d' = d := by unfold indexShift at hD; split_ifs at hD <;> omega
    rw [ec, ed, ea, eb, hcd, trainDown_self, one_mul, mul_one]
  by_cases h1 : max a b + 1 ≤ min c d ∨ max c d + 1 ≤ min a b
  · -- Case 1: the letter is far from every letter of the train.
    have ec : c' = c := by unfold indexShift at hC; split_ifs at hC <;> omega
    have eb : b' = b := by unfold indexShift at hB; split_ifs at hB <;> omega
    have ea : a' = a := by unfold indexShift at hA; split_ifs at hA <;> omega
    have ed : d' = d := by unfold indexShift at hD; split_ifs at hD <;> omega
    rw [ec, ed, ea, eb]
    rcases hab with rfl | rfl
    · rw [trainUp_succ_self]
      exact trainDown_far_comm_inv h hb (by omega) hc hck hd hdk (by omega)
    · rw [trainUp_self_succ]
      exact trainDown_far_comm h ha (by omega) hc hck hd hdk (by omega)
  rcases Nat.lt_or_ge c d with hlt | hge
  · -- The negative train, `c < d`.
    by_cases h4 : min a b = d
    · -- Case 4 for `c < d`: the letter sits at the train's tail.
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      rcases hab with rfl | rfl
      · have hbe : b = e + 1 := by omega
        have ec : c' = c := by unfold indexShift at hC; split_ifs at hC <;> omega
        have eb : b' = e := by unfold indexShift at hB; split_ifs at hB <;> omega
        have ea : a' = e + 2 := by unfold indexShift at hA; split_ifs at hA <;> omega
        have ed : d' = e := by unfold indexShift at hD; split_ifs at hD <;> omega
        rw [ec, ed, ea, eb, hbe, trainUp_succ_self]
        exact h.gen_split_neg_inv hc (by omega) (by omega)
      · have hae : a = e + 1 := by omega
        have ec : c' = c := by unfold indexShift at hC; split_ifs at hC <;> omega
        have eb : b' = e + 2 := by unfold indexShift at hB; split_ifs at hB <;> omega
        have ea : a' = e := by unfold indexShift at hA; split_ifs at hA <;> omega
        have ed : d' = e + 2 := by unfold indexShift at hD; split_ifs at hD <;> omega
        rw [ec, ed, ea, eb, hae, trainUp_self_succ]
        exact h.gen_split_neg hc (by omega) (by omega)
    · -- Case 2 for `c < d`: the letter's index shifts down by one.
      have hpos : c + 1 ≤ min a b ∧ min a b + 1 ≤ d := by omega
      have ec : c' = c := by unfold indexShift at hC; split_ifs at hC <;> omega
      have eb : b = b' + 1 := by unfold indexShift at hB; split_ifs at hB <;> omega
      have ea : a = a' + 1 := by unfold indexShift at hA; split_ifs at hA <;> omega
      have ed : d' = d := by unfold indexShift at hD; split_ifs at hD <;> omega
      rw [ec, ed, ea, eb]
      rcases hab with hsign | hsign
      · have ha' : a' = b' + 1 := by omega
        rw [ha', trainUp_succ_self, trainUp_succ_self]
        exact h.gen_shift_neg_inv hc (by omega) (by omega) hdk
      · have hb' : b' = a' + 1 := by omega
        rw [hb', trainUp_self_succ, trainUp_self_succ]
        exact h.gen_shift_neg hc (by omega) (by omega) hdk
  · -- The positive train, `d < c`.
    by_cases h4 : min a b + 1 = d
    · -- Case 4 for `d < c`: the letter sits just below the train's tail.
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      rcases hab with rfl | rfl
      · have hbe : b = e := by omega
        have ec : c' = c := by unfold indexShift at hC; split_ifs at hC <;> omega
        have eb : b' = e := by unfold indexShift at hB; split_ifs at hB <;> omega
        have ea : a' = e + 2 := by unfold indexShift at hA; split_ifs at hA <;> omega
        have ed : d' = e := by unfold indexShift at hD; split_ifs at hD <;> omega
        rw [ec, ed, ea, eb, hbe, trainUp_succ_self]
        exact h.gen_split_pos_inv (by omega) (by omega) hck
      · have hae : a = e := by omega
        have ec : c' = c := by unfold indexShift at hC; split_ifs at hC <;> omega
        have eb : b' = e + 2 := by unfold indexShift at hB; split_ifs at hB <;> omega
        have ea : a' = e := by unfold indexShift at hA; split_ifs at hA <;> omega
        have ed : d' = e + 2 := by unfold indexShift at hD; split_ifs at hD <;> omega
        rw [ec, ed, ea, eb, hae, trainUp_self_succ]
        exact h.gen_split_pos (by omega) (by omega) hck
    · -- Case 2 for `d < c`: the letter's index shifts up by one.
      have hpos : d ≤ min a b ∧ min a b + 2 ≤ c := by omega
      have ec : c' = c := by unfold indexShift at hC; split_ifs at hC <;> omega
      have eb : b' = b + 1 := by unfold indexShift at hB; split_ifs at hB <;> omega
      have ea : a' = a + 1 := by unfold indexShift at hA; split_ifs at hA <;> omega
      have ed : d' = d := by unfold indexShift at hD; split_ifs at hD <;> omega
      rw [ec, ed, ea, eb]
      rcases hab with rfl | rfl
      · rw [trainUp_succ_self, trainUp_succ_self]
        exact h.gen_shift_pos_inv hd (by omega) (by omega) hck
      · rw [trainUp_self_succ, trainUp_self_succ]
        exact h.gen_shift_pos hd (by omega) (by omega) hck

/-! ### The index bookkeeping of the induction -/

/-- The three live clauses of `HJO.Braid.indexShift` at an argument different from the second index,
each with the condition that selects it. Splitting on this rather than unfolding two nested shifts
at once is what keeps the case analysis below finite. -/
private theorem indexShift_eq_cases (p q x : ℤ) (hx : x ≠ q) :
    (p ≤ x ∧ x < q ∧ indexShift p q x = x + 1) ∨ (q < x ∧ x ≤ p ∧ indexShift p q x = x - 1) ∨
      (¬(p ≤ x ∧ x < q) ∧ ¬(q < x ∧ x ≤ p) ∧ indexShift p q x = x) := by
  unfold indexShift
  split_ifs <;> omega

/-- The four straddling configurations, as pure arithmetic. When `b̂` and `b` are adjacent, both
differ from `c`, and their images under `σ_{d,c}` are *not* adjacent, the pair `{b̂, b}` must
straddle the end `d` of the train, and then the two images are `d - ε` and `d + ε`. Stated
separately from
`HJO.Braid.collide_step_facts` because the case analysis is nine-way and wants a context with no
shifts in it. -/
private theorem straddle_values {a b c d bh a₁ b₁ : ℤ}
    (hstep : (a + 2 ≤ b ∧ bh = b - 1) ∨ (b + 2 ≤ a ∧ bh = b + 1)) (hbc : b ≠ c) (hbhc : bh ≠ c)
    (hA : (d ≤ bh ∧ bh < c ∧ a₁ = bh + 1) ∨ (c < bh ∧ bh ≤ d ∧ a₁ = bh - 1) ∨
      (¬(d ≤ bh ∧ bh < c) ∧ ¬(c < bh ∧ bh ≤ d) ∧ a₁ = bh))
    (hB : (d ≤ b ∧ b < c ∧ b₁ = b + 1) ∨ (c < b ∧ b ≤ d ∧ b₁ = b - 1) ∨
      (¬(d ≤ b ∧ b < c) ∧ ¬(c < b ∧ b ≤ d) ∧ b₁ = b))
    (hstr : ¬(a₁ = b₁ + 1 ∨ b₁ = a₁ + 1)) :
    (a₁ = d - 1 ∧ b₁ = d + 1 ∧ a ≤ d - 1 ∧ ((d < c ∧ bh = d - 1) ∨ (c < d ∧ bh = d))) ∨
      (a₁ = d + 1 ∧ b₁ = d - 1 ∧ d + 1 ≤ a ∧ ((d < c ∧ bh = d) ∨ (c < d ∧ bh = d + 1))) := by
  rcases hA with ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ <;>
    rcases hB with ⟨q1, q2, q3⟩ | ⟨q1, q2, q3⟩ | ⟨q1, q2, q3⟩ <;> omega

/-- **The five index identities the induction of `HJO.Braid.IsBraidSystem.collide` rests on.**
Peeling the last letter off `T_{a↗b}` replaces one collision by two: first the letter `T_{b̂↗b}`
against `T_{c↘d}`, giving `(a₁,b₁,c₁,d₁)`, and then the shortened train `T_{a↗b̂}` against the new
`T_{c₁↘d₁}`, giving `(a₂,b₂,c₂,d₂)`. For the two to compose into the single collision of `(a,b,c,d)`
five things must hold, and they are the five conjuncts here: `b̂ ≠ c₁`, so that the second collision
is legitimate; `b₂ = a₁`, so that the two short ascending trains glue; and `c₂ = c'`, `a₂ = a'`,
`d₂ = d'`.

One can verify these in the four cases of `HJO.Braid.IsBraidSystem.collide_base`.
Two observations shorten
that to the three cases below. First, `HJO.Braid.indexShift_ne_head` says `a₁ = σ_{d,c}(b̂) ≠ d`,
and `d₁ = σ_{a₁,b₁}(d)` moves `d` only when `a₁ = d`; so `d₁ = d` whenever `a₁` and `b₁` are
adjacent, which makes three of the five conjuncts immediate and the fifth one application of
`HJO.Braid.indexShift_congr_tail`. Second, `a₁` and `b₁` fail to be adjacent exactly when `{b̂, b}`
straddles the end `d` of the train — the Case 4 — and there all four indices are known
explicitly. The Cases 1 and 2 are therefore not distinguished here at all. -/
private theorem collide_step_facts {a b c d bh a₁ b₁ c₁ d₁ : ℤ}
    (hstep : (a + 2 ≤ b ∧ bh = b - 1) ∨ (b + 2 ≤ a ∧ bh = b + 1)) (hbc : b ≠ c)
    (hcol : collideIndex bh b c d = (a₁, b₁, c₁, d₁)) :
    bh ≠ c₁ ∧ indexShift d₁ c₁ bh = a₁ ∧ indexShift a bh c₁ = indexShift a b c ∧
      indexShift d₁ (indexShift a b c) a = indexShift d (indexShift a b c) a ∧
      indexShift (indexShift d (indexShift a b c) a) a₁ d₁
        = indexShift (indexShift d (indexShift a b c) a) b₁ d := by
  rw [collideIndex_eq] at hcol
  simp only [Prod.mk.injEq] at hcol
  obtain ⟨hA, hB, hC, hD⟩ := hcol
  rw [hC] at hA
  rw [hC, hA, hB] at hD
  have hadj : bh = b + 1 ∨ b = bh + 1 := by rcases hstep with ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega
  have hb1d : b₁ ≠ d := by rw [← hB]; exact indexShift_ne_head hbc
  have hcc : indexShift a b c ≠ a := indexShift_ne_head (Ne.symm hbc)
  by_cases hbhc : bh = c
  · -- The letter starts at the head of the train: `c₁ = b` and `a₁ = b₁`.
    have hc1 : c₁ = b := by unfold indexShift at hC; split_ifs at hC <;> omega
    have habs : |b - c| = 1 := by rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]; omega
    have habs' : |c - b| = 1 := by rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]; omega
    have ha1b1 : a₁ = b₁ :=
      calc a₁ = indexShift d b c := by rw [← hA, hc1, hbhc]
        _ = indexShift d c b := indexShift_comm_adjacent habs
        _ = b₁ := hB
    have hd1 : d₁ = d := by unfold indexShift at hD; split_ifs at hD <;> omega
    refine ⟨by omega, by rw [hd1]; exact hA, ?_, by rw [hd1], by rw [ha1b1, hd1]⟩
    calc indexShift a bh c₁ = indexShift a c b := by rw [hc1, hbhc]
      _ = indexShift a b c := indexShift_comm_adjacent habs'
  · -- The letter is not at the head of the train, so `c₁ = c`.
    have hc1 : c₁ = c := by unfold indexShift at hC; split_ifs at hC <;> omega
    rw [hc1] at hA
    have ha1d : a₁ ≠ d := by rw [← hA]; exact indexShift_ne_head hbhc
    have hF3 : indexShift a bh c₁ = indexShift a b c := by
      rw [hc1]
      exact indexShift_congr_tail (by rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]; omega)
        (by omega) (by omega)
    have hD' := indexShift_eq_cases a₁ b₁ d (Ne.symm hb1d)
    rw [hD] at hD'
    by_cases hstr : a₁ = b₁ + 1 ∨ b₁ = a₁ + 1
    · -- `a₁` and `b₁` are adjacent, so the tail of the train does not move.
      have hd1 : d₁ = d := by omega
      refine ⟨by omega, by rw [hd1, hc1]; exact hA, hF3, by rw [hd1], ?_⟩
      rw [hd1]
      exact indexShift_congr_tail (by rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]; omega)
        (by omega) (by omega)
    · -- `{b̂, b}` straddles the tail `d`: the Case 4.
      have hA' := indexShift_eq_cases d c bh hbhc
      have hB' := indexShift_eq_cases d c b hbc
      rw [hA] at hA'
      rw [hB] at hB'
      have hpos := straddle_values hstep hbc hbhc hA' hB' hstr
      have hd1 : d₁ = b₁ := by omega
      obtain ⟨A, hAeq⟩ : ∃ A, indexShift d (indexShift a b c) a = A := ⟨_, rfl⟩
      have hAbound : A = a - 1 ∨ A = a ∨ A = a + 1 := by
        have hcases := indexShift_eq_cases d (indexShift a b c) a (Ne.symm hcc)
        rw [hAeq] at hcases
        omega
      rw [hAeq]
      refine ⟨by omega, ?_, hF3, ?_, ?_⟩
      · rw [hd1, hc1]
        have hcases := indexShift_eq_cases b₁ c bh hbhc
        omega
      · rw [← hAeq]
        refine (indexShift_congr_head ?_ (Ne.symm hcc) ?_ ?_).symm
        · rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]; omega
        · omega
        · omega
      · have h5a := indexShift_eq_cases A a₁ d₁ (by omega)
        have h5b := indexShift_eq_cases A b₁ d (Ne.symm hb1d)
        omega

/-! ### The general collision -/

/-- **Collision**, `HJO.Braid.IsBraidSystem.collide`, as an induction on `|a - b|` with the rank
carried along. The `n = 0` case has both ascending trains empty; `n = 1` is
`HJO.Braid.IsBraidSystem.collide_base`; and the step glues `T_{a↗b} = T_{a↗b̂}T_{b̂↗b}`, collides
the one-letter factor with the train by the base case, and applies the inductive hypothesis to what
is left, the five index identities of `HJO.Braid.collide_step_facts` saying that the two collisions
compose into the one asked for. -/
private theorem collide_aux (h : IsBraidSystem k T Tinv) (n : ℕ) :
    ∀ a b c d a' b' c' d' : ℕ, (a - b) + (b - a) = n →
      1 ≤ a → a ≤ k → 1 ≤ b → b ≤ k → 1 ≤ c → c ≤ k → 1 ≤ d → d ≤ k → b ≠ c →
      collideIndex (a : ℤ) (b : ℤ) (c : ℤ) (d : ℤ) = ((a' : ℤ), (b' : ℤ), (c' : ℤ), (d' : ℤ)) →
      trainUp T Tinv a b * trainDown T Tinv c d
        = trainDown T Tinv c' d' * trainUp T Tinv a' b' := by
  induction n with
  | zero =>
    intro a b c d a' b' c' d' hn ha hak hb hbk hc hck hd hdk hbc hcol
    have hab0 : a = b := by omega
    rw [collideIndex_eq] at hcol
    simp only [Prod.mk.injEq] at hcol
    obtain ⟨hA, hB, hC, hD⟩ := hcol
    rw [hC] at hA
    rw [hC, hA, hB] at hD
    have hc1 : c' = c := by unfold indexShift at hC; split_ifs at hC <;> omega
    rw [hc1] at hA
    have habZ : (a' : ℤ) = (b' : ℤ) := by rw [← hA, ← hB, hab0]
    have hab' : a' = b' := by exact_mod_cast habZ
    have hb'd : (b' : ℤ) ≠ (d : ℤ) := by
      rw [← hB]; exact indexShift_ne_head (by exact_mod_cast hbc)
    have hd1 : d' = d := by unfold indexShift at hD; split_ifs at hD <;> omega
    rw [hc1, hd1, hab', hab0, trainUp_self, trainUp_self, one_mul, mul_one]
  | succ n ih =>
    intro a b c d a' b' c' d' hn ha hak hb hbk hc hck hd hdk hbc hcol
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · exact h.collide_base ha hak hb hbk hc hck hd hdk (by omega) hbc hcol
    obtain ⟨bh, hbh, hbhk, hstepN⟩ : ∃ bh : ℕ, 1 ≤ bh ∧ bh ≤ k ∧
        ((a + 2 ≤ b ∧ bh + 1 = b) ∨ (b + 2 ≤ a ∧ bh = b + 1)) := by
      rcases Nat.lt_or_ge a b with hlt | hge
      · exact ⟨b - 1, by omega, by omega, Or.inl ⟨by omega, by omega⟩⟩
      · exact ⟨b + 1, by omega, by omega, Or.inr ⟨by omega, rfl⟩⟩
    obtain ⟨a₁, b₁, c₁, d₁, hq1, hq2, hq3, hq4, hcol1⟩ :=
      exists_nat_collideIndex hbh hbhk hb hbk hc hck hd hdk
    have hbase := h.collide_base hbh hbhk hb hbk hc hck hd hdk (by omega) hbc hcol1
    obtain ⟨hF1, hF2, hF3, hF4, hF5⟩ :=
      collide_step_facts (a := (a : ℤ)) (by omega) (by exact_mod_cast hbc) hcol1
    have hbhc1 : bh ≠ c₁ := by exact_mod_cast hF1
    obtain ⟨a₂, b₂, c₂, d₂, hs1, hs2, hs3, hs4, hcol2⟩ :=
      exists_nat_collideIndex ha hak hbh hbhk hq3.1 hq3.2 hq4.1 hq4.2
    have hih := ih a bh c₁ d₁ a₂ b₂ c₂ d₂ (by omega) ha hak hbh hbhk hq3.1 hq3.2 hq4.1 hq4.2
      hbhc1 hcol2
    -- The components of the three collisions.
    have hcol1c := hcol1
    rw [collideIndex_eq] at hcol1c hcol hcol2
    simp only [Prod.mk.injEq] at hcol1c hcol hcol2
    obtain ⟨hA1, hB1, hC1, hD1⟩ := hcol1c
    obtain ⟨hA, hB, hC, hD⟩ := hcol
    obtain ⟨hA2, hB2, hC2, hD2⟩ := hcol2
    rw [hA, hB1] at hD
    rw [hF3] at hA2 hC2 hD2
    rw [hF4] at hA2 hD2
    rw [hA] at hA2 hD2 hF5
    rw [hF2] at hB2 hD2
    -- The four index identities the assembly needs.
    have hb2 : a₁ = b₂ := by exact_mod_cast hB2
    have hc2 : c' = c₂ := by rw [hC] at hC2; exact_mod_cast hC2
    have ha2 : a' = a₂ := by exact_mod_cast hA2
    have hb1 : b' = b₁ := by rw [hB] at hB1; exact_mod_cast hB1
    have hd2 : d₂ = d' := by
      have hd2Z : (d₂ : ℤ) = (d' : ℤ) := by rw [← hD2, hF5, hD]
      exact_mod_cast hd2Z
    -- The assembly.
    have hglue1 : trainUp T Tinv a bh * trainUp T Tinv bh b = trainUp T Tinv a b :=
      trainUp_mul_trainUp h ha hak hbh hbhk hb hbk
    have hglue2 : trainUp T Tinv a₂ b₂ * trainUp T Tinv a₁ b₁ = trainUp T Tinv a₂ b₁ := by
      rw [hb2]; exact trainUp_mul_trainUp h hs1.1 hs1.2 hs2.1 hs2.2 hq2.1 hq2.2
    calc trainUp T Tinv a b * trainDown T Tinv c d
        = trainUp T Tinv a bh * (trainUp T Tinv bh b * trainDown T Tinv c d) := by
          rw [← hglue1, mul_assoc]
      _ = trainUp T Tinv a bh * (trainDown T Tinv c₁ d₁ * trainUp T Tinv a₁ b₁) := by rw [hbase]
      _ = trainUp T Tinv a bh * trainDown T Tinv c₁ d₁ * trainUp T Tinv a₁ b₁ :=
          (mul_assoc _ _ _).symm
      _ = trainDown T Tinv c₂ d₂ * trainUp T Tinv a₂ b₂ * trainUp T Tinv a₁ b₁ := by rw [hih]
      _ = trainDown T Tinv c₂ d₂ * (trainUp T Tinv a₂ b₂ * trainUp T Tinv a₁ b₁) := mul_assoc _ _ _
      _ = trainDown T Tinv c₂ d₂ * trainUp T Tinv a₂ b₁ := by rw [hglue2]
      _ = trainDown T Tinv c' d' * trainUp T Tinv a' b' := by rw [← hc2, hd2, ← ha2, ← hb1]

/-- **Collision**, `HJO.Braid.IsBraidSystem.collide`: for `b ≠ c` and the collision indices
`(a',b',c',d')` of `HJO.Braid.collideIndex`,
`T_{a↗b} T_{c↘d} = T_{c'↘d'} T_{a'↗b'}`, with no restriction on `|a - b|`.

The induction is on `|a - b|`, peeling the last letter off the ascending train; the base case is
`HJO.Braid.IsBraidSystem.collide_base` and the bookkeeping that the two collisions so produced
compose into this one is `HJO.Braid.collide_step_facts`. -/
@[hjo "lem_train_collide"]
theorem IsBraidSystem.collide (h : IsBraidSystem k T Tinv) {a b c d a' b' c' d' : ℕ}
    (ha : 1 ≤ a) (hak : a ≤ k) (hb : 1 ≤ b) (hbk : b ≤ k) (hc : 1 ≤ c) (hck : c ≤ k)
    (hd : 1 ≤ d) (hdk : d ≤ k) (hbc : b ≠ c)
    (hcol : collideIndex (a : ℤ) (b : ℤ) (c : ℤ) (d : ℤ)
      = ((a' : ℤ), (b' : ℤ), (c' : ℤ), (d' : ℤ))) :
    trainUp T Tinv a b * trainDown T Tinv c d
      = trainDown T Tinv c' d' * trainUp T Tinv a' b' :=
  collide_aux h ((a - b) + (b - a)) a b c d a' b' c' d' rfl ha hak hb hbk hc hck hd hdk hbc hcol

end HJO.Braid
