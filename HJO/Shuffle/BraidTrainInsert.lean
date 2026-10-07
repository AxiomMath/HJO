/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidClosedForms
public meta import HJO.Attr

/-! # Trains against the train based at `1`

The braid computation behind Mellit's Proposition 5.7 — inserting a fixed point at the start — moves
everything past the descending train `T_{i↘1}` that the inserted strand contributes. This file is
the abstract layer of that computation: identities about a braid system, all of them consequences of
`HJO.Braid.trainUp_overtake`, `HJO.Braid.trainUp_mul_trainUp`, `HJO.Braid.trainDown_mul_trainDown`
and `HJO.Braid.trainDown_far_comm`, and none of them mentioning the braid monoid or the inserted
point.

## Main results

* `HJO.Braid.trainDown_overtake` — overtaking for *descending* trains,
  `T_{a↘b}T_{c↘d} = T_{c↘d}T_{a+1↘b+1}` for `d ≤ a, b < c`. This is `HJO.Braid.trainUp_overtake` for
  the letterwise inverses, read back through `HJO.Braid.trainUp_inv_eq_trainDown`.
* `HJO.Braid.trainDown_one_mul_trainDown_one` — the case the insertion uses,
  `T_{a↘1}T_{c↘1} = T_{c↘1}T_{a+1↘2}` for `a < c`: passing the inserted train raises the index.
* `HJO.Braid.gen_mul_trainDown_one` — the one-letter form, `T_rT_{c↘1} = T_{c↘1}T_{r+1}` for
  `r + 2 ≤ c`, and `HJO.Braid.trainDown_one_mul_gen` the same read from the other side.
* `HJO.Braid.trainDown_two_mul_trainUp_one_of_le` and
  `HJO.Braid.trainDown_two_mul_trainUp_one_of_ge` — the two regimes of `T_{c↘2}T_{1↗a+1}`: it is
  `T_{1↗a}T_{c↘1}` when `a + 1 ≤ c` and `T_{1↗a+1}T_{c-1↘1}` when `c ≤ a + 1`. These are the two
  index cases in the proof of Proposition 5.7, and which one fires is what decides whether the
  inserted point's rank changes.
* `HJO.Braid.comm_trainDown` — an element commuting with every letter of a descending train
  commutes with the train.
* `HJO.Braid.trainDown_one_mul_trainDown_one_four`,
  `HJO.Braid.trainDown_two_mul_trainUp_one_of_le_three`,
  `HJO.Braid.trainDown_two_mul_trainUp_one_of_ge_three` — the three formulas written out in letters
  at the smallest index where they say something, as orientation checks.

## Implementation notes

`HJO.Braid.trainDown_two_mul_trainUp_one_of_ge` is stated at `c = e + 1` rather than with `c - 1` in
the conclusion, `ℕ`-subtraction being no part of the statement; its hypothesis `1 ≤ e` is
`2 ≤ c`.

Both regimes are inductions on the length of the ascending train, whose step is the one-letter shift
`HJO.Braid.trainDown_one_mul_gen` in the first case and far commutation in the second. The two agree
at the boundary `a + 1 = c`, where `T_{1↗a}T_{c↘1} = T_{1↗a+1}T_{c-1↘1}` by one gluing at each end;
the second regime's base case *is* that computation.

## References

Transcribing the train arithmetic in the proof of A. Mellit, *Toric braids and `(m, n)`-parking
functions*, Proposition 5.7.
-/

@[expose] public section

namespace HJO.Braid

variable {M : Type*} [Monoid M] {k : ℕ} {T Tinv : ℕ → M}

/-! ### Lengthening a train by one letter -/

/-- `T_{1↗a}T_a = T_{1↗a+1}`: the ascending train based at `1` grows by its top letter. -/
theorem trainUp_one_mul_gen (h : IsBraidSystem k T Tinv) {a : ℕ} (ha : 1 ≤ a) (hak : a + 1 ≤ k) :
    trainUp T Tinv 1 a * T a = trainUp T Tinv 1 (a + 1) := by
  have hglue := trainUp_mul_trainUp (T := T) (Tinv := Tinv) h (a := 1) (b := a) (c := a + 1)
    (by omega) (by omega) ha (by omega) (by omega) hak
  rwa [show trainUp T Tinv a (a + 1) = T a from trainUp_self_succ T Tinv a] at hglue

/-- `T_{c↘2}T_1 = T_{c↘1}`: the descending train based at `2` grows by the bottom letter. -/
theorem trainDown_two_mul_gen (h : IsBraidSystem k T Tinv) {c : ℕ} (hc : 2 ≤ c) (hck : c ≤ k) :
    trainDown T Tinv c 2 * T 1 = trainDown T Tinv c 1 := by
  have hglue := trainDown_mul_trainDown (T := T) (Tinv := Tinv) h (a := c) (b := 2) (c := 1)
    (by omega) hck (by omega) (by omega) (by omega) (by omega)
  rwa [show trainDown T Tinv 2 1 = T 1 from trainDown_succ_self T Tinv 1] at hglue

/-- `T_{c+1↘c}T_{c↘1} = T_{c+1↘1}`: the descending train based at `1` grows by its top letter. -/
theorem gen_mul_trainDown_one_eq (h : IsBraidSystem k T Tinv) {c : ℕ} (hc : 1 ≤ c)
    (hck : c + 1 ≤ k) : T c * trainDown T Tinv c 1 = trainDown T Tinv (c + 1) 1 := by
  have hglue := trainDown_mul_trainDown (T := T) (Tinv := Tinv) h (a := c + 1) (b := c) (c := 1)
    (by omega) hck hc (by omega) (by omega) (by omega)
  rwa [show trainDown T Tinv (c + 1) c = T c from trainDown_succ_self T Tinv c] at hglue

/-! ### Overtaking, descending -/

/-- **Overtaking for descending trains**: for `1 ≤ d ≤ a, b < c ≤ k`,
`T_{a↘b}T_{c↘d} = T_{c↘d}T_{a+1↘b+1}`.

`HJO.Braid.trainUp_inv_eq_trainDown` reads a descending train as an ascending train of the
letterwise inverses, and `HJO.Braid.IsBraidSystem.inverses` says those form a braid system, so this
is `HJO.Braid.trainUp_overtake` for that system. -/
theorem trainDown_overtake (h : IsBraidSystem k T Tinv) {a b c d : ℕ} (hd : 1 ≤ d) (hda : d ≤ a)
    (hac : a < c) (hdb : d ≤ b) (hbc : b < c) (hck : c ≤ k) :
    trainDown T Tinv a b * trainDown T Tinv c d
      = trainDown T Tinv c d * trainDown T Tinv (a + 1) (b + 1) := by
  simp only [← trainUp_inv_eq_trainDown]
  exact trainUp_overtake h.inverses hd hda hac hdb hbc hck

/-- **The case the insertion uses**: `T_{a↘1}T_{c↘1} = T_{c↘1}T_{a+1↘2}` for `1 ≤ a < c ≤ k`.

Both trains are based at `1`, and passing the longer one raises the shorter one's two indices by
`1`: this is the mechanism by which the conjugation of Proposition 5.7 implements the index shift of
`HJO.Braid.phiPlusStar`. -/
theorem trainDown_one_mul_trainDown_one (h : IsBraidSystem k T Tinv) {a c : ℕ} (ha : 1 ≤ a)
    (hac : a < c) (hck : c ≤ k) :
    trainDown T Tinv a 1 * trainDown T Tinv c 1
      = trainDown T Tinv c 1 * trainDown T Tinv (a + 1) 2 :=
  trainDown_overtake h le_rfl ha hac le_rfl (by omega) hck

/-- **The one-letter form**: `T_rT_{c↘1} = T_{c↘1}T_{r+1}` for `1 ≤ r`, `r + 2 ≤ c ≤ k`. The letter
has to stay two below the head of the train, `T_{c-1}T_{c↘1} = T_{c↘1}T_c` being false. -/
theorem gen_mul_trainDown_one (h : IsBraidSystem k T Tinv) {r c : ℕ} (hr : 1 ≤ r)
    (hrc : r + 2 ≤ c) (hck : c ≤ k) :
    T r * trainDown T Tinv c 1 = trainDown T Tinv c 1 * T (r + 1) := by
  have h1 := trainDown_overtake h (a := r + 1) (b := r) (c := c) (d := 1) le_rfl (by omega)
    (by omega) (by omega) (by omega) hck
  rwa [trainDown_succ_self, trainDown_succ_self] at h1

/-- `HJO.Braid.gen_mul_trainDown_one` read from the other side: `T_{c↘1}T_{r+1} = T_rT_{c↘1}`. -/
theorem trainDown_one_mul_gen (h : IsBraidSystem k T Tinv) {r c : ℕ} (hr : 1 ≤ r)
    (hrc : r + 2 ≤ c) (hck : c ≤ k) :
    trainDown T Tinv c 1 * T (r + 1) = T r * trainDown T Tinv c 1 :=
  (gen_mul_trainDown_one h hr hrc hck).symm

/-! ### The two regimes of `T_{c↘2}T_{1↗a+1}` -/

/-- **The ascending train stops below the descending one**: for `1 ≤ a`, `a + 1 ≤ c ≤ k`,
`T_{c↘2}T_{1↗a+1} = T_{1↗a}T_{c↘1}`.

Induction on `a`. The base `a = 1` is one gluing, `T_{c↘2}T_1 = T_{c↘1}`; the step lengthens the
ascending train by `T_{a+1}` on the right and moves that letter across the descending train by
`HJO.Braid.trainDown_one_mul_gen`, which turns it into `T_a` and so lengthens the *left* train by
the letter one lower. -/
theorem trainDown_two_mul_trainUp_one_of_le (h : IsBraidSystem k T Tinv) :
    ∀ a, 1 ≤ a → ∀ {c : ℕ}, a + 1 ≤ c → c ≤ k →
      trainDown T Tinv c 2 * trainUp T Tinv 1 (a + 1)
        = trainUp T Tinv 1 a * trainDown T Tinv c 1 := by
  intro a ha
  induction a, ha using Nat.le_induction with
  | base =>
    intro c hc hck
    rw [show trainUp T Tinv 1 (1 + 1) = T 1 from trainUp_self_succ T Tinv 1,
      trainDown_two_mul_gen h (by omega) hck,
      show trainUp T Tinv 1 1 = 1 from trainUp_self T Tinv 1, one_mul]
  | succ a ha ih =>
    intro c hc hck
    rw [← trainUp_one_mul_gen h (by omega) (by omega : a + 1 + 1 ≤ k), ← mul_assoc,
      ih (by omega) hck, mul_assoc, trainDown_one_mul_gen h ha (by omega) hck, ← mul_assoc,
      trainUp_one_mul_gen h ha (by omega)]

/-- **The ascending train reaches past the descending one**: for `1 ≤ e ≤ a`, `a + 1 ≤ k`,
`T_{e+1↘2}T_{1↗a+1} = T_{1↗a+1}T_{e↘1}`.

Induction on `a` from `a = e`, where the claim is
`HJO.Braid.trainDown_two_mul_trainUp_one_of_le` at its boundary followed by one gluing at each end.
The step lengthens the ascending train by a letter that is *far* from every letter of `T_{e↘1}`, so
this regime moves nothing: the head of the descending train has been passed already. -/
theorem trainDown_two_mul_trainUp_one_of_ge (h : IsBraidSystem k T Tinv) {e : ℕ} (he : 1 ≤ e) :
    ∀ a, e ≤ a → a + 1 ≤ k →
      trainDown T Tinv (e + 1) 2 * trainUp T Tinv 1 (a + 1)
        = trainUp T Tinv 1 (a + 1) * trainDown T Tinv e 1 := by
  intro a hea
  induction a, hea using Nat.le_induction with
  | base =>
    intro hek
    rw [trainDown_two_mul_trainUp_one_of_le h e he (by omega) hek,
      ← gen_mul_trainDown_one_eq h he hek, ← mul_assoc, trainUp_one_mul_gen h he hek]
  | succ a hea ih =>
    intro hak
    rw [← trainUp_one_mul_gen h (by omega) (by omega : a + 1 + 1 ≤ k), ← mul_assoc,
      ih (by omega), mul_assoc, mul_assoc]
    congr 1
    exact (trainDown_far_comm h (i := a + 1) (a := e) (b := 1) (by omega) (by omega) he
      (by omega) (by omega) (by omega) (by omega)).symm

/-! ### The three identities at small indices

Each general formula written out in letters at the smallest index where it says something, checked
against the words Mellit's notation names. An orientation error in any of the three — a train read
backwards, or an index shifted the wrong way — would make the corresponding statement below false,
the expansions of the trains being independent of the formulas being checked. -/

/-- `T_{2↘1}T_{4↘1} = T_{4↘1}T_{3↘2}` reads `T_1·T_3T_2T_1 = T_3T_2T_1·T_2`: the short train's two
indices both rise by one as it passes the long one. -/
theorem trainDown_one_mul_trainDown_one_four (h : IsBraidSystem k T Tinv) (hk : 4 ≤ k) :
    T 1 * (T 3 * T 2 * T 1) = T 3 * T 2 * T 1 * T 2 := by
  have hid := trainDown_one_mul_trainDown_one h (a := 2) (c := 4) (by omega) (by omega) hk
  rwa [show trainDown T Tinv 2 1 = T 1 from trainDown_succ_self T Tinv 1,
    show trainDown T Tinv 4 1 = T 3 * T 2 * T 1 from trainDown_four_one T Tinv,
    show trainDown T Tinv 3 2 = T 2 from trainDown_succ_self T Tinv 2] at hid

/-- `T_{3↘2}T_{1↗3} = T_{1↗2}T_{3↘1}` reads `T_2·T_1T_2 = T_1·T_2T_1`: the ascending train stops
below the descending one, so the descending train comes out based at `1` and the ascending one loses
its top letter. -/
theorem trainDown_two_mul_trainUp_one_of_le_three (h : IsBraidSystem k T Tinv) (hk : 3 ≤ k) :
    T 2 * (T 1 * T 2) = T 1 * (T 2 * T 1) := by
  have hid := trainDown_two_mul_trainUp_one_of_le h 2 (by omega) (c := 3) (by omega) hk
  rwa [show trainDown T Tinv 3 2 = T 2 from trainDown_succ_self T Tinv 2,
    show trainUp T Tinv 1 3 = T 1 * T 2 by simp [trainUp, ascendingWord, List.range'],
    show trainUp T Tinv 1 2 = T 1 from trainUp_self_succ T Tinv 1,
    show trainDown T Tinv 3 1 = T 2 * T 1 by simp [trainDown, descendingWord, List.range']] at hid

/-- `T_{3↘2}T_{1↗4} = T_{1↗4}T_{2↘1}` reads `T_2·T_1T_2T_3 = T_1T_2T_3·T_1`: the ascending train
reaches past the descending one, so the ascending train survives intact and the descending one comes
out one index lower. -/
theorem trainDown_two_mul_trainUp_one_of_ge_three (h : IsBraidSystem k T Tinv) (hk : 4 ≤ k) :
    T 2 * (T 1 * T 2 * T 3) = T 1 * T 2 * T 3 * T 1 := by
  have hid := trainDown_two_mul_trainUp_one_of_ge h (e := 2) (by omega) 3 (by omega) (by omega)
  rwa [show trainDown T Tinv 3 2 = T 2 from trainDown_succ_self T Tinv 2,
    show trainUp T Tinv 1 4 = T 1 * T 2 * T 3 from trainUp_one_four T Tinv,
    show trainDown T Tinv 2 1 = T 1 from trainDown_succ_self T Tinv 1] at hid

/-! ### Commuting with a train -/

/-- **An element commuting with every letter of a descending train commutes with the train.** Stated
for the descending branch `b ≤ a`, which is where the letters are the uninverted `T_j` for
`b ≤ j < a`; this is how `z_1` and `ỹ_1` are moved across `T_{c↘2}`. -/
theorem comm_trainDown {x : M} {a b : ℕ} (hba : b ≤ a)
    (hT : ∀ j, b ≤ j → j < a → x * T j = T j * x) :
    x * trainDown T Tinv a b = trainDown T Tinv a b * x := by
  have hw : trainDown T Tinv a b = descendingWord T a b := by
    rw [trainDown]
    split_ifs
    rfl
  rw [hw, descendingWord]
  refine mul_prod_comm fun y hy => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
  rw [List.mem_reverse, List.mem_range'_1] at hj
  exact hT j (by omega) (by omega)

end HJO.Braid

end
