/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepShiftConjugate
public meta import HJO.Attr

/-!
# The correction word propagates: each sweep generator moves it up by one letter

`HJO/Shuffle/SweepShiftConjugate.lean` computes the residual of the round-grouping at a
**single** base event of an extension: with `Σ_δ = HJO.Sweep.shiftAux` and
`T_{[1,δ]} = HJO.Sweep.cmAscWord q 1 δ`,

`O^{ext}_P(g·Σ_δ F) = c_P · T_{[1,δ]}^{ε_P}(g·Σ_δ(O^{base}_P F))`,

with `ε_P = 1` at rules `A` and `C` and `ε_P = 0` at `B`, `D`, `E`. The value is **not** back in the
form `g'·Σ_δ F'`, so the next event's comparison does not apply to it: the word has to be moved out
of the way first. This file does that.

## Main results

* `HJO.Sweep.cmAscWord_mul_cmAscWord_succ`: **the general word shift.**
  `T_{[1,n]}·T_{[c+1,c+d]} = T_{[c+2,c+d+1]}·T_{[1,n]}` for `c + d + 1 ≤ n`. The lemma
  `HJO.Sweep.cmAscWord_word_shift` is the case `c = 0`, `d = n - 1`; the general range is what the
  propagation needs, because the word it has to move has already been shifted by the events before
  it.
* `HJO.Sweep.dminus_cmAscWord_range`: **`d^♭_-` passes the word unchanged**, for `c + d ≤ m`:
  `d^♭_-{}^{(m+2)}(T_{[c+1,c+d]}F) = T_{[c+1,c+d]}(d^♭_-{}^{(m+2)}F)`. This is
  `HJO.Sweep.dminus_cmAscWord` with the left end of the range freed.
* `HJO.Sweep.dplus_cmAscWord`: **`d^♭_+` passes the word and shifts every letter up by one**, for
  `c + d + 1 ≤ n`:
  `d^♭_+{}^{(n)}(T_{[c+1,c+d]}F) = T_{[c+2,c+d+1]}(d^♭_+{}^{(n)}F)`.
* `HJO.Sweep.corner_cmAscWord`: **`Δ` does the same**, for `c + d + 2 ≤ n`:
  `Δ^{(n)}(T_{[c+1,c+d]}F) = T_{[c+2,c+d+1]}(Δ^{(n)}F)`.

At the level of `HJO.Mellit.sweepOperator` these are `HJO.Mellit.sweepOperator_cmAscWord_A`,
`_B`, `_C`, `_D`, `_E`: the sweep operator at a point moves `T_{[c+1,c+δ]}` leftwards, shifting it
to
`T_{[c+2,c+δ+1]}` at rules `A` and `C` and leaving it alone at `B`, `D` and `E`, under a bound on
`c + δ` against `HJO.Paths.sweepWidth` at that point.

## The accumulated word: the descending staircase

Reading a layer of `HJO.Mellit.roundSweepWord` right to left and using the per-event comparison and
these commutations alternately, the accumulated correction after `m` events of type `A` or `C` is
the
**descending staircase**

`T_{[m,m+δ-1]} ⋯ T_{[2,δ+1]}·T_{[1,δ]}`,

one block per type-`A`-or-`C` event, each block the previous one's letters raised by one; rules `B`,
`D` and `E` contribute no block and shift nothing. `HJO.Sweep.stairWord q δ c m` is this word at
offset `c`, `HJO.Sweep.stairWord_succ_shift` is the recursion that closes the propagation, and
`HJO.Sweep.dplus_stairWord`, `HJO.Sweep.dminus_stairWord`, `HJO.Sweep.corner_stairWord` (and the
`HJO.Mellit.sweepOperator` forms `HJO.Mellit.sweepOperator_stairWord_A`…`_E`) move a whole staircase
past one generator. At `δ = 1` the staircase is the descending word `T_m ⋯ T_1`.

## What this closes: a whole base layer, transported

`HJO.Mellit.exists_layerWord_shiftAux` is the payoff. For a list `ℓ` of base points on which the
width shift is the single integer `δ` — which by
`HJO.Mellit.sweepWidth_appendHeights_of_diagExcess_eq` is exactly a round's base layer, and which by
`HJO.Mellit.baseRoundWord_appendHeights` is read on the base's own list in the base's own order —

`(∏_{P ∈ ℓ} O^{ext}_P)(g·Σ_δF) = q^s · S_{0,m}(g·Σ_δ((∏_{P ∈ ℓ} O^{base}_P)F))`

with `m ≤ #ℓ` and `s = δ·(#D − #C)`. So the low factor and the shift **do** come back out of a whole
layer, and the entire discrepancy between the extension's base layer and the base's own word is one
staircase and one power of `q`. `q ≠ 0` is read only to add the exponents of rules `C` and `D`,
whose
scalars are inverse.

**The one thing that is not free is a width side condition.** The staircase arriving at an event `P`
has one block per type-`A`-or-`C` event applied before `P`, so its top letter sits at
`#r + δ - 1` where `r` is the suffix of the layer applied before `P`, and moving it past the
extension's operator at index `sweepWidth z P + δ` costs `#r + 1 ≤ sweepWidth z P`. The shift `δ`
cancels out of the comparison, and the sharp form counts only the type-`A`-or-`C` events of `r`.
Geometrically it says the staircase must not reach the variable the operator reads: the staircase's
letters run over `y_1, …, y_{#r+δ}` while the operator at `P` reads `y_{sweepWidth z P + δ}`.

**By `HJO.Mellit.roundSweepWord_split_fst` the events of `r` are the layer's points of higher
abscissa** — inside a round the rank order is the abscissa order and the low-abscissa part stands
leftmost, so is applied last. So the condition compares the number of the layer's type-`A`-or-`C`
points strictly to the right of `P` with the number of live north steps at `P`, and
`HJO.Paths.sweepRight` counts exactly the live north steps strictly to the right of `P` — with the
step whose foot is `P` live at a type-`C` event and *not* counted by it. That is the shape the
condition should be discharged in. It is a statement about the base path alone, with no `a`, no `A`,
no `q`, no `u` and no coprimality, which is what the window coupling `HJO.Paths.tailLiveSteps`
predicts: the per-event and per-layer work is parameter-free, and `a` enters only at the round
boundary, where the tail layers reconcile `Σ_{δ_{e+1}}` with `Σ_{δ_e}`.

**The width does not satisfy a `±1` recursion along a layer**, because a round reorders the sweep:
consecutive points of one excess level are `(a, b)` apart and the events between them belong to
other
levels. So the condition cannot be reduced to the width at the layer's first event.

## What this does not close

The tail layers of `HJO.Mellit.roundSweepWord_split_fst`, the reconciliation of consecutive shifts
between rounds (`HJO.Paths.card_liveSteps_high_appendHeights_ne` exhibits two tails of one fibre
with
corrections `2` and `1`), and the final match of the accumulated staircases against
`HJO.Mellit.stageTotal` are all untouched. The letter shift `T_i ↦ T_{i+1}` that the staircase is
built from is the same shift that `HJO.Sweep.shiftAux_braid` derives from the variable shift, and
`HJO.Sweep.dplusStar` carries `HJO.Sweep.cycleShift`, `y_i ↦ y_{i+1}`, on the other side — so the
two
sides carry corrections of one kind, which is a reason to expect the match. It is not the match.

## References

This file builds on `HJO.Sweep.cmAscWord`, `HJO.Sweep.cmAscWord_split`,
`HJO.Sweep.cmAscWord_mul_braidEnd`, `HJO.Sweep.cmAscWord_word_shift`, `HJO.Sweep.dminus`,
`HJO.Sweep.dplus`, `HJO.Sweep.corner`, `HJO.Mellit.sweepOperator`, `HJO.Paths.sweepWidth`.
Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*, sections 3 and 4.
-/

@[expose] public section

namespace HJO.Sweep

/-! ### The general word shift -/

section WordShift

variable {L : Type*} [Field L]

/-- **THE GENERAL WORD SHIFT.** For `c + d + 1 ≤ n`,

`T_{[1,n]}·T_{[c+1,c+d]} = T_{[c+2,c+d+1]}·T_{[1,n]}`.

The long word `T_{[1,n]}` moves each letter of the short word up by one
(`HJO.Sweep.cmAscWord_mul_braidEnd`), and raising the index range `[c+1, c+d]` by one gives
`[c+2, c+d+1]` (`HJO.Braid.mul_ascendingWord`, which performs both steps).

The earlier `HJO.Sweep.cmAscWord_word_shift` is the case `c = 0`, `d = n - 1`. The general left end
is
what the propagation along a layer needs: the word arriving at the `j`-th event has already been
raised `j - 1` times, so its range starts at `j` rather than at `1`, and the case `c = 0` no longer
applies to it.

No relation beyond the `S_3` relation at a single letter and the two far commutations is read, so
there is no hypothesis on `q` — in particular not `q ≠ 0`, which
`HJO.Sweep.isBraidSystem_braidEnd` would need. -/
@[hjo "lem_cm_word_shift_general"]
theorem cmAscWord_mul_cmAscWord_succ (q : L) {n c d : ℕ} (hn : c + d + 1 ≤ n) :
    cmAscWord q 1 n * cmAscWord q (c + 1) (c + d)
      = cmAscWord q (c + 2) (c + d + 1) * cmAscWord q 1 n := by
  rw [cmAscWord_eq_ascendingWord q (a := c + 1) (b := c + d) (by omega),
    cmAscWord_eq_ascendingWord q (a := c + 2) (b := c + d + 1) (by omega),
    show c + d + 1 + 1 = c + d + 1 + 1 from rfl]
  have key := Braid.mul_ascendingWord (T := braidEnd q) (W := cmAscWord q 1 n)
    (a := c + 1) (b := c + d + 1) (by omega)
    (fun i _ hib => cmAscWord_mul_braidEnd q (by omega) (by omega))
  exact key

/-- **`T_{[1,n]}(T_{[c+1,c+d]}F) = T_{[c+2,c+d+1]}(T_{[1,n]}F)`**, the applied form of
`HJO.Sweep.cmAscWord_mul_cmAscWord_succ`. -/
theorem cmAscWord_cmAscWord_succ (q : L) {n c d : ℕ} (hn : c + d + 1 ≤ n) (F : Total L) :
    cmAscWord q 1 n (cmAscWord q (c + 1) (c + d) F)
      = cmAscWord q (c + 2) (c + d + 1) (cmAscWord q 1 n F) :=
  LinearMap.congr_fun (cmAscWord_mul_cmAscWord_succ q hn) F

end WordShift

/-! ### The raising operator passes the word and shifts it -/

section Raising

variable {L : Type*} [Field L]

/-- **`d^♭_+` PASSES THE WORD AND SHIFTS IT UP BY ONE LETTER.** For `c + d + 1 ≤ n`,

`d^♭_+{}^{(n)}(T_{[c+1,c+d]}F) = T_{[c+2,c+d+1]}(d^♭_+{}^{(n)}F)`.

This is the companion of `HJO.Sweep.dminus_cmAscWord` for the raising operator, and it is **not** a
commutation: the word comes out shifted. `d^♭_+{}^{(n)}` is `-T_{[1,n]}` after `y_{n+1}τ_{n+1}`; the
substitution and the multiplier both pass the word untouched, every letter being at most `n - 1` and
so distant from `y_{n+1}` (`HJO.Sweep.qshift_cmAscWord`,
`HJO.Sweep.cmAscWord_mul_of_swapAux_eq` through `HJO.Sweep.swapAux_auxVar_of_ne`), and then the long
word `T_{[1,n]}` shifts it by `HJO.Sweep.cmAscWord_mul_cmAscWord_succ`.

No hypothesis on `q` and none on `F`. The bound `c + d + 1 ≤ n` is exactly what keeps the *shifted*
word's top letter `c + d + 1` inside the long word. -/
@[hjo "lem_sweep_dplus_word_shift"]
theorem dplus_cmAscWord (q : L) {n c d : ℕ} (hn : c + d + 1 ≤ n) (F : Total L) :
    dplus q n (cmAscWord q (c + 1) (c + d) F)
      = cmAscWord q (c + 2) (c + d + 1) (dplus q n F) := by
  have hfix : ∀ j, c + 1 ≤ j → j ≤ c + d →
      swapAux L j (auxVar (n + 1) : Total L) = auxVar (n + 1) :=
    fun j _ hj2 => swapAux_auxVar_of_ne (by omega) (by omega) (by omega)
  rw [dplus_eq_ascWord, dplus_eq_ascWord, map_neg,
    qshift_cmAscWord q (a := c + 1) (b := c + d) (m := n + 1) (by omega) (by omega),
    ← cmAscWord_mul_of_swapAux_eq q (a := c + 1) (b := c + d) (by omega) hfix,
    cmAscWord_cmAscWord_succ q hn]

end Raising

/-! ### The lowering operator passes the word unchanged -/

section Lowering

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`d^♭_-` PASSES THE WORD UNCHANGED**, for `c + d ≤ m`:

`d^♭_-{}^{(m+2)}(T_{[c+1,c+d]}F) = T_{[c+1,c+d]}(d^♭_-{}^{(m+2)}F)`.

`HJO.Sweep.dminus_cmAscWord` with the left end of the index range freed: every letter `T_j` of the
word has `j ≤ c + d ≤ m`, which is the index `HJO.Sweep.dminus_braid` covers, and an element
commuting with every letter commutes with the product (`HJO.Braid.mul_prod_comm`).

**The asymmetry with `HJO.Sweep.dplus_cmAscWord` is real and is what makes the accumulated word a
staircase rather than a power**: `d^♭_-` leaves the word where it is, `d^♭_+` and `Δ` raise it. -/
theorem dminus_mul_cmAscWord_range (q : L) {c d m : ℕ} (hm : c + d ≤ m) :
    dminus q (m + 2) * cmAscWord q (c + 1) (c + d)
      = cmAscWord q (c + 1) (c + d) * dminus q (m + 2) := by
  rw [cmAscWord_eq_ascendingWord q (by omega), Braid.ascendingWord]
  refine Braid.mul_prod_comm fun y hy => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
  rw [List.mem_range'_1] at hj
  exact dminus_mul_braidEnd q (by omega)

/-- `d^♭_-{}^{(m+2)}(T_{[c+1,c+d]}F) = T_{[c+1,c+d]}(d^♭_-{}^{(m+2)}F)`, the applied form. -/
@[hjo "lem_sweep_dminus_word_pass"]
theorem dminus_cmAscWord_range (q : L) {c d m : ℕ} (hm : c + d ≤ m) (F : Total L) :
    dminus q (m + 2) (cmAscWord q (c + 1) (c + d) F)
      = cmAscWord q (c + 1) (c + d) (dminus q (m + 2) F) :=
  LinearMap.congr_fun (dminus_mul_cmAscWord_range q hm) F

end Lowering

/-! ### The corner operator passes the word and shifts it -/

section Corner

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`Δ` PASSES THE WORD AND SHIFTS IT UP BY ONE LETTER**, for `c + d + 2 ≤ n`:

`Δ^{(n)}(T_{[c+1,c+d]}F) = T_{[c+2,c+d+1]}(Δ^{(n)}F)`.

Both terms of the commutator `Δ = (q-1)^{-1}(d^♭_-d^♭_+ - d^♭_+d^♭_-)` come out with the same
shifted
word, so it factors out: in `d^♭_-{}^{(n+1)}d^♭_+{}^{(n)}` the raising half shifts the word
(`HJO.Sweep.dplus_cmAscWord`) and the lowering half then passes the shifted word
(`HJO.Sweep.dminus_cmAscWord_range` at `c + 1`); in `d^♭_+{}^{(n-1)}d^♭_-{}^{(n)}` the lowering half
passes the word first and the raising half shifts it afterwards.

**The bound is one stronger than `HJO.Sweep.dplus_cmAscWord`'s**, `c + d + 2 ≤ n` rather than
`c + d + 1 ≤ n`, because `d^♭_-{}^{(n+1)}` reaches only letters `≤ n - 1` and the word it must pass
has already been shifted to top letter `c + d + 1`. That one unit is the whole of the side condition
the propagation along a layer carries.

No hypothesis on `q` — in particular not `q ≠ 1`, both sides being `(q-1)^{-1}` times the same
polynomial identity. -/
@[hjo "lem_sweep_corner_word_shift"]
theorem corner_cmAscWord (q : L) {n c d : ℕ} (hn : c + d + 2 ≤ n) (F : Total L) :
    corner q n (cmAscWord q (c + 1) (c + d) F)
      = cmAscWord q (c + 2) (c + d + 1) (corner q n F) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h1 : dminus q (m + 2 + 1) (dplus q (m + 2) (cmAscWord q (c + 1) (c + d) F))
      = cmAscWord q (c + 2) (c + d + 1) (dminus q (m + 2 + 1) (dplus q (m + 2) F)) := by
    rw [dplus_cmAscWord q (show c + d + 1 ≤ m + 2 from by omega),
      show m + 2 + 1 = (m + 1) + 2 from by omega,
      show c + 2 = (c + 1) + 1 from by omega, show c + d + 1 = (c + 1) + d from by omega,
      dminus_cmAscWord_range q (show (c + 1) + d ≤ m + 1 from by omega)]
  have h2 : dplus q (m + 2 - 1) (dminus q (m + 2) (cmAscWord q (c + 1) (c + d) F))
      = cmAscWord q (c + 2) (c + d + 1) (dplus q (m + 2 - 1) (dminus q (m + 2) F)) := by
    rw [dminus_cmAscWord_range q (show c + d ≤ m from by omega),
      dplus_cmAscWord q (show c + d + 1 ≤ m + 2 - 1 from by omega)]
  rw [corner_of_pos q (show m + 2 ≠ 0 from by omega)]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply]
  rw [h1, h2, ← map_sub, ← map_smul]

end Corner

/-! ### The accumulated word: the descending staircase -/

section Stair

variable {L : Type*} [Field L]

/-- **The staircase word `T_{[c+m,c+m+δ-1]} ⋯ T_{[c+2,c+δ+1]}·T_{[c+1,c+δ]}`**, the correction
accumulated by `m` type-`A`-or-`C` events of one layer at shift `δ`, with every letter raised by the
offset `c`.

Each block is the previous one with every letter raised by one, which is exactly what
`HJO.Sweep.dplus_cmAscWord` and `HJO.Sweep.corner_cmAscWord` do to the word they pass, and the
innermost block `T_{[c+1,c+δ]}` is what `HJO.Sweep.dplus_shiftAux_mul` and
`HJO.Sweep.corner_shiftAux_mul` produce at the event itself. Rules `B`, `D` and `E` contribute no
block and shift nothing (`HJO.Sweep.dminus_cmAscWord_range`), so `m` counts type-`A` and type-`C`
events only.

The offset is what makes the recursion close: passing the staircase through one more type-`A`
or type-`C` event raises `c` by one (`HJO.Sweep.dplus_stairWord`, `HJO.Sweep.corner_stairWord`) and
then `HJO.Sweep.stairWord_succ_shift` puts the new block back at offset `c`. The accumulated word of
a whole layer is `stairWord q δ 0 m`; at `δ = 1` it is the descending word `T_m ⋯ T_1`, the shape
the
`a = 1` band identity was closed with, and at `δ = 0` it is the identity. -/
@[hjo "def_sweep_stair_word"]
noncomputable def stairWord (q : L) (δ c : ℕ) : ℕ → Module.End L (Total L)
  | 0 => 1
  | m + 1 => cmAscWord q (c + m + 1) (c + m + δ) * stairWord q δ c m

@[hjo "def_sweep_stair_word", simp]
theorem stairWord_zero (q : L) (δ c : ℕ) : stairWord q δ c 0 = 1 := rfl

/-- **One step of the staircase**: `S_{c,m+1} = T_{[c+m+1,c+m+δ]}·S_{c,m}`. -/
@[hjo "def_sweep_stair_word"]
theorem stairWord_succ (q : L) (δ c m : ℕ) :
    stairWord q δ c (m + 1) = cmAscWord q (c + m + 1) (c + m + δ) * stairWord q δ c m := rfl

/-- `HJO.Sweep.stairWord_succ` applied to a vector. -/
theorem stairWord_succ_apply (q : L) (δ c m : ℕ) (X : Total L) :
    stairWord q δ c (m + 1) X = cmAscWord q (c + m + 1) (c + m + δ) (stairWord q δ c m X) := rfl

/-- The staircase at `δ = 0` is the identity: every block is the empty word. -/
theorem stairWord_zero_shift (q : L) (c m : ℕ) : stairWord q 0 c m = 1 := by
  induction m with
  | zero => rfl
  | succ n ih =>
    rw [stairWord_succ, ih, mul_one]
    exact cmAscWord_self_pred q (c + n)

/-- The staircase of height `1` is the single block the first type-`A`-or-`C` event produces. -/
theorem stairWord_one (q : L) (δ c : ℕ) : stairWord q δ c 1 = cmAscWord q (c + 1) (c + δ) := by
  rw [stairWord_succ, stairWord_zero, mul_one]
  simp

/-- **THE STAIRCASE RECURSION.** `S_{c+1,m}·T_{[c+1,c+δ]} = S_{c,m+1}`.

This is what closes the propagation: an event of type `A` or `C` raises the staircase already
accumulated by one offset and produces a fresh block at offset `c`, and the two together are the
staircase of height one greater at the original offset. -/
@[hjo "lem_sweep_stair_recursion"]
theorem stairWord_succ_shift (q : L) (δ c m : ℕ) :
    stairWord q δ (c + 1) m * cmAscWord q (c + 1) (c + δ) = stairWord q δ c (m + 1) := by
  induction m with
  | zero => rw [stairWord_zero, one_mul, stairWord_one]
  | succ n ih =>
    rw [stairWord_succ, mul_assoc, ih, stairWord_succ (m := n + 1),
      show c + 1 + n + 1 = c + (n + 1) + 1 from by omega,
      show c + 1 + n + δ = c + (n + 1) + δ from by omega]

/-- `HJO.Sweep.stairWord_succ_shift` applied to a vector. -/
theorem stairWord_succ_shift_apply (q : L) (δ c m : ℕ) (X : Total L) :
    stairWord q δ (c + 1) m (cmAscWord q (c + 1) (c + δ) X) = stairWord q δ c (m + 1) X :=
  LinearMap.congr_fun (stairWord_succ_shift q δ c m) X

/-- `HJO.Sweep.stairWord_succ_shift_apply` at offset `0`, the only offset a layer's accumulated word
is read at: `S_{1,m}(T_{[1,δ]}X) = S_{0,m+1}X`. -/
theorem stairWord_succ_shift_zero_apply (q : L) (δ m : ℕ) (X : Total L) :
    stairWord q δ 1 m (cmAscWord q 1 δ X) = stairWord q δ 0 (m + 1) X := by
  have h := stairWord_succ_shift_apply q δ 0 m X
  simpa using h

end Stair

/-! ### The three generators pass a whole staircase -/

section StairPass

variable {L : Type*} [Field L]

/-- **`d^♭_+` passes a whole staircase and raises its offset by one**, for `c + m + δ ≤ n`:

`d^♭_+{}^{(n)}(S_{c,m}X) = S_{c+1,m}(d^♭_+{}^{(n)}X)`.

Block by block through `HJO.Sweep.dplus_cmAscWord`. The bound is the outermost block's:
its top letter is `c + m + δ - 1`, which after the shift is `c + m + δ`, and that must stay inside
the long word `T_{[1,n]}` of `d^♭_+{}^{(n)}`. -/
theorem dplus_stairWord (q : L) {δ c n : ℕ} (m : ℕ) (hm : c + m + δ ≤ n) (X : Total L) :
    dplus q n (stairWord q δ c m X) = stairWord q δ (c + 1) m (dplus q n X) := by
  induction m with
  | zero => simp
  | succ p ih =>
    rw [stairWord_succ_apply, dplus_cmAscWord q (c := c + p) (d := δ) (by omega),
      ih (by omega), stairWord_succ_apply (c := c + 1),
      show c + 1 + p + 1 = c + p + 2 from by omega,
      show c + 1 + p + δ = c + p + δ + 1 from by omega]

end StairPass

section StairPassNewton

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`d^♭_-` passes a whole staircase unchanged**, for `c + m + δ + 1 ≤ n`:

`d^♭_-{}^{(n)}(S_{c,m}X) = S_{c,m}(d^♭_-{}^{(n)}X)`.

Block by block through `HJO.Sweep.dminus_cmAscWord_range`. The bound is one stronger than
`HJO.Sweep.dplus_stairWord`'s because `d^♭_-{}^{(n)}` reaches only the letters `T_j` with
`j ≤ n - 2`. -/
theorem dminus_stairWord (q : L) {δ c n : ℕ} (m : ℕ) (hm : c + m + δ + 1 ≤ n) (X : Total L) :
    dminus q n (stairWord q δ c m X) = stairWord q δ c m (dminus q n X) := by
  induction m with
  | zero => simp
  | succ p ih =>
    obtain ⟨J, rfl⟩ : ∃ J, n = J + 2 := ⟨n - 2, by omega⟩
    rw [stairWord_succ_apply, dminus_cmAscWord_range q (show c + p + δ ≤ J from by omega),
      ih (by omega), stairWord_succ_apply]

/-- **`Δ` passes a whole staircase and raises its offset by one**, for `c + m + δ + 1 ≤ n`:

`Δ^{(n)}(S_{c,m}X) = S_{c+1,m}(Δ^{(n)}X)`.

Block by block through `HJO.Sweep.corner_cmAscWord`, and with that lemma's bound, one unit stronger
than `HJO.Sweep.dplus_stairWord`'s. -/
theorem corner_stairWord (q : L) {δ c n : ℕ} (m : ℕ) (hm : c + m + δ + 1 ≤ n) (X : Total L) :
    corner q n (stairWord q δ c m X) = stairWord q δ (c + 1) m (corner q n X) := by
  induction m with
  | zero => simp
  | succ p ih =>
    rw [stairWord_succ_apply, corner_cmAscWord q (c := c + p) (d := δ) (by omega),
      ih (by omega), stairWord_succ_apply (c := c + 1),
      show c + 1 + p + 1 = c + p + 2 from by omega,
      show c + 1 + p + δ = c + p + δ + 1 from by omega]

end StairPassNewton

end HJO.Sweep

/-! ### The propagation at a point of the sweep -/

namespace HJO.Mellit

open HJO.Sweep HJO.Paths Finset

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {a b N : ℕ}

section Propagate

variable {y : Heights a b N} {P : ℕ × ℕ}

/-- **Rule `A` moves the word leftwards and raises it.** For `c + d + 1 ≤ sweepWidth y P`,

`O_P(T_{[c+1,c+d]}X) = T_{[c+2,c+d+1]}(O_PX)`.

`HJO.Sweep.dplus_cmAscWord` read through `HJO.Mellit.sweepOperator_of_eventType_A`. -/
theorem sweepOperator_cmAscWord_A (hA : eventType y P = EventType.A) {c d : ℕ}
    (hc : c + d + 1 ≤ sweepWidth y P) (X : Total L) :
    sweepOperator q u y P (cmAscWord q (c + 1) (c + d) X)
      = cmAscWord q (c + 2) (c + d + 1) (sweepOperator q u y P X) := by
  rw [sweepOperator_of_eventType_A y hA]
  exact dplus_cmAscWord q hc X

/-- **Rule `B` moves the word leftwards unchanged.** For `c + d + 2 ≤ sweepWidth y P`,

`O_P(T_{[c+1,c+d]}X) = T_{[c+1,c+d]}(O_PX)`.

`HJO.Sweep.dminus_cmAscWord_range` read through `HJO.Mellit.sweepOperator_of_eventType_B`. The bound
is one stronger than rule `A`'s: `d^♭_-{}^{(k)}` reaches only the letters `T_j` with `j ≤ k - 2`. -/
theorem sweepOperator_cmAscWord_B (hB : eventType y P = EventType.B) {c d : ℕ}
    (hc : c + d + 2 ≤ sweepWidth y P) (X : Total L) :
    sweepOperator q u y P (cmAscWord q (c + 1) (c + d) X)
      = cmAscWord q (c + 1) (c + d) (sweepOperator q u y P X) := by
  rw [sweepOperator_of_eventType_B y hB, show sweepWidth y P = (sweepWidth y P - 2) + 2 from by
    omega]
  exact dminus_cmAscWord_range q (by omega) X

/-- **Rule `C` moves the word leftwards and raises it.** For `c + d + 2 ≤ sweepWidth y P`,

`O_P(T_{[c+1,c+d]}X) = T_{[c+2,c+d+1]}(O_PX)`.

`HJO.Sweep.corner_cmAscWord` read through `HJO.Mellit.sweepOperator_of_eventType_C`; the scalar
`q^{-a_P}` is central and rides along. -/
theorem sweepOperator_cmAscWord_C (hC : eventType y P = EventType.C) {c d : ℕ}
    (hc : c + d + 2 ≤ sweepWidth y P) (X : Total L) :
    sweepOperator q u y P (cmAscWord q (c + 1) (c + d) X)
      = cmAscWord q (c + 2) (c + d + 1) (sweepOperator q u y P X) := by
  rw [sweepOperator_of_eventType_C y hC]
  simp only [LinearMap.smul_apply]
  rw [corner_cmAscWord q hc X, map_smul]

/-- **Rule `D` moves the word leftwards unchanged**, being a scalar. No bound at all. -/
theorem sweepOperator_cmAscWord_D (hD : eventType y P = EventType.D) (c d : ℕ) (X : Total L) :
    sweepOperator q u y P (cmAscWord q (c + 1) (c + d) X)
      = cmAscWord q (c + 1) (c + d) (sweepOperator q u y P X) := by
  rw [sweepOperator_of_eventType_D y hD]
  simp only [LinearMap.smul_apply, Module.End.one_apply, map_smul]

/-- **Rule `E` moves the word leftwards unchanged**, being a scalar. No bound at all. -/
theorem sweepOperator_cmAscWord_E (hE : eventType y P = EventType.E) (c d : ℕ) (X : Total L) :
    sweepOperator q u y P (cmAscWord q (c + 1) (c + d) X)
      = cmAscWord q (c + 1) (c + d) (sweepOperator q u y P X) := by
  rw [sweepOperator_of_eventType_E q u y P hE]
  simp only [LinearMap.smul_apply, Module.End.one_apply, map_smul]

/-! ### The sweep operator passes a whole staircase -/

/-- **Rule `A` passes the accumulated staircase and raises its offset.** For
`m + δ ≤ sweepWidth y P`. -/
theorem sweepOperator_stairWord_A (hA : eventType y P = EventType.A) {δ m : ℕ}
    (hm : m + δ ≤ sweepWidth y P) (X : Total L) :
    sweepOperator q u y P (stairWord q δ 0 m X) = stairWord q δ 1 m (sweepOperator q u y P X) := by
  rw [sweepOperator_of_eventType_A y hA]
  have h := dplus_stairWord q (δ := δ) (c := 0) (n := sweepWidth y P) m (by omega) X
  simpa using h

/-- **Rule `B` passes the accumulated staircase unchanged.** For
`m + δ + 1 ≤ sweepWidth y P`. -/
theorem sweepOperator_stairWord_B (hB : eventType y P = EventType.B) {δ m : ℕ}
    (hm : m + δ + 1 ≤ sweepWidth y P) (X : Total L) :
    sweepOperator q u y P (stairWord q δ 0 m X) = stairWord q δ 0 m (sweepOperator q u y P X) := by
  rw [sweepOperator_of_eventType_B y hB]
  exact dminus_stairWord q m (by omega) X

/-- **Rule `C` passes the accumulated staircase and raises its offset.** For
`m + δ + 1 ≤ sweepWidth y P`. -/
theorem sweepOperator_stairWord_C (hC : eventType y P = EventType.C) {δ m : ℕ}
    (hm : m + δ + 1 ≤ sweepWidth y P) (X : Total L) :
    sweepOperator q u y P (stairWord q δ 0 m X) = stairWord q δ 1 m (sweepOperator q u y P X) := by
  rw [sweepOperator_of_eventType_C y hC]
  simp only [LinearMap.smul_apply]
  have h := corner_stairWord q (δ := δ) (c := 0) (n := sweepWidth y P) m (by omega) X
  rw [h, map_smul]

/-- **Rule `D` passes the accumulated staircase unchanged**, being a scalar. No bound. -/
theorem sweepOperator_stairWord_D (hD : eventType y P = EventType.D) (δ m : ℕ) (X : Total L) :
    sweepOperator q u y P (stairWord q δ 0 m X) = stairWord q δ 0 m (sweepOperator q u y P X) := by
  rw [sweepOperator_of_eventType_D y hD]
  simp only [LinearMap.smul_apply, Module.End.one_apply, map_smul]

/-- **Rule `E` passes the accumulated staircase unchanged**, being a scalar. No bound. -/
theorem sweepOperator_stairWord_E (hE : eventType y P = EventType.E) (δ m : ℕ) (X : Total L) :
    sweepOperator q u y P (stairWord q δ 0 m X) = stairWord q δ 0 m (sweepOperator q u y P X) := by
  rw [sweepOperator_of_eventType_E q u y P hE]
  simp only [LinearMap.smul_apply, Module.End.one_apply, map_smul]

end Propagate

/-! ### The whole base layer of a round, transported to the base's own widths -/

section Layer

variable {N A : ℕ} {z : Heights a b N} {w : Heights a b A}

/-- **THE LAYER PROPAGATION.** For a list `ℓ` of base points on which the width shift is the single
integer `δ` — which by `HJO.Mellit.sweepWidth_appendHeights_of_diagExcess_eq` is what a round's base
layer is — the extension's layer word applied to `g·Σ_δF` is a power of `q` times a **staircase**
applied to `Σ_δ` of the base's own layer word applied to `F`:

`(∏_{P ∈ ℓ} O^{ext}_P)(g·Σ_δF) = q^s · S_{0,m}(g·Σ_δ((∏_{P ∈ ℓ} O^{base}_P)F))`

with `m ≤ #ℓ` the number of type-`A`-or-`C` events of the layer and `s` the integer
`δ·(#D − #C)`. So the low factor `g` and the shift `Σ_δ` do come back out, and the whole discrepancy
between the extension's base layer and the base's own word is the staircase and the scalar.

This is the propagation the per-event comparisons of
`HJO/Shuffle/SweepShiftConjugate.lean` left open. Its ingredients are the five per-event
comparisons, the five staircase commutations `HJO.Mellit.sweepOperator_stairWord_A`…`_E`, and the
recursion `HJO.Sweep.stairWord_succ_shift`.

**The hypothesis `hwid` is the side condition, and it is the only thing here that is not free.** It
asks, of each event `P` of the layer, that the base width there exceed the number of events of the
layer applied *before* `P` — the events standing to the right of `P` in the product, which is the
suffix `r` of the decomposition `ℓ = v ++ P :: r`. The staircase arriving at `P` has one block per
type-`A`-or-`C` event of `r`, so its top letter is at `#r + δ - 1`, and passing it through the
extension's operator at index `sweepWidth z P + δ` is exactly this comparison. Note that it is
**independent of `δ`**: both sides of the bound carry the shift, so it cancels.

What the induction really consumes is the sharper `#{type-A-or-C events of r} + 1 ≤ sweepWidth z P`;
`#r` stands in for it only to avoid counting event types. By
`HJO.Mellit.roundSweepWord_split_fst` the events of `r` are the layer's points of *higher* abscissa,
so the sharp bound compares the number of the layer's type-`A`-or-`C` points strictly to the right
of
`P` with the number of live north steps at `P` — and `HJO.Paths.sweepRight` counts exactly the live
north steps strictly to the right of `P`, the step with foot `P` being live at a type-`C` event and
not counted by it. That is the shape in which the condition should be discharged. It carries **no**
`a`, no `A`, no `q`, no `u` and no coprimality, which is what the window coupling
`HJO.Paths.tailLiveSteps` predicts: the per-event work is parameter-free and `a` enters only at the
round boundary, where the tail layers reconcile `Σ_{δ_{e+1}}` with `Σ_{δ_e}`.

The width does **not** satisfy a `±1` recursion along a layer — a round reorders the sweep, and
consecutive points of one excess level are `(a, b)` apart with the events between them belonging to
other levels — so the condition does not reduce to the width at the layer's first event. It is
vacuous whenever a round's base layer is a single point, which is the case at the worked instance
`a = 1`, `A = 1`, `N = 1` of `HJO/Shuffle/SweepAppendBandOneB.lean`, where there is one point
of
each kind per level.

`q ≠ 0` is read only to add the exponents of rules `C` and `D`, whose scalars are inverse. -/
theorem exists_layerWord_shiftAux (hq : q ≠ 0) (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w)
    (hN : 0 < N) (δ : ℕ) {g : Total L} (hgaux : g ∈ auxSubalg L) (hgp : g ∈ piece L δ)
    (F : Total L) :
    ∀ ℓ : List (ℕ × ℕ), (∀ P ∈ ℓ, P.1 < a * N) →
      (∀ P ∈ ℓ, #(tailLiveSteps w (diagExcess a b P)) = δ) →
      (∀ v r : List (ℕ × ℕ), ∀ P : ℕ × ℕ, ℓ = v ++ P :: r → r.length + 1 ≤ sweepWidth z P) →
      ∃ (m : ℕ) (s : ℤ), m ≤ ℓ.length ∧
        (ℓ.map (sweepOperator q u (appendHeights z w))).prod (g * shiftAux L δ F)
          = q ^ s • stairWord q δ 0 m
              (g * shiftAux L δ ((ℓ.map (sweepOperator q u z)).prod F)) := by
  intro ℓ
  induction ℓ with
  | nil =>
    intro _ _ _
    exact ⟨0, 0, Nat.zero_le _, by simp⟩
  | cons x t ih =>
    intro hlow hδ hwid
    obtain ⟨m, s, hmt, heq⟩ := ih
      (fun P hP => hlow P (List.mem_cons_of_mem _ hP))
      (fun P hP => hδ P (List.mem_cons_of_mem _ hP))
      (fun v r P h => hwid (x :: v) r P (by rw [h]; rfl))
    have hxmem : x ∈ x :: t := List.mem_cons_self ..
    have hlowx : x.1 < a * N := hlow x hxmem
    have hδx : #(tailLiveSteps w (diagExcess a b x)) = δ := hδ x hxmem
    have hwidx : t.length + 1 ≤ sweepWidth z x := hwid [] t x rfl
    have hwext : sweepWidth (appendHeights z w) x = sweepWidth z x + δ := by
      rw [sweepWidth_appendHeights_eq hz hw hN hlowx, hδx]
    have hgpx : g ∈ piece L (#(tailLiveSteps w (diagExcess a b x))) := by rw [hδx]; exact hgp
    have htyp : eventType (appendHeights z w) x = eventType z x :=
      eventType_appendHeights (by omega)
    have hbA : m + δ ≤ sweepWidth (appendHeights z w) x := by rw [hwext]; omega
    have hbB : m + δ + 1 ≤ sweepWidth (appendHeights z w) x := by rw [hwext]; omega
    set Y : Total L := (t.map (sweepOperator q u z)).prod F with hY
    have hLc : ((x :: t).map (sweepOperator q u (appendHeights z w))).prod (g * shiftAux L δ F)
        = sweepOperator q u (appendHeights z w) x
            ((t.map (sweepOperator q u (appendHeights z w))).prod (g * shiftAux L δ F)) := by
      rw [List.map_cons, List.prod_cons]; rfl
    have hRc : ((x :: t).map (sweepOperator q u z)).prod F = sweepOperator q u z x Y := by
      rw [List.map_cons, List.prod_cons, hY]; rfl
    cases hevx : eventType z x with
    | A =>
      refine ⟨m + 1, s, by simp only [List.length_cons]; omega, ?_⟩
      have hev := sweepOperator_shiftAux_appendHeights_A (q := q) (u := u) hz hw hN hlowx hevx
        hgaux hgpx Y
      rw [hδx] at hev
      rw [hLc, heq, map_smul,
        sweepOperator_stairWord_A (htyp.trans hevx) hbA, hev,
        stairWord_succ_shift_zero_apply, hRc]
    | B =>
      refine ⟨m, s, by simp only [List.length_cons]; omega, ?_⟩
      have hev := sweepOperator_shiftAux_appendHeights_B (q := q) (u := u) hz hw hN hlowx
        (by omega) hevx hgaux hgpx Y
      rw [hδx] at hev
      rw [hLc, heq, map_smul,
        sweepOperator_stairWord_B (htyp.trans hevx) hbB, hev, hRc]
    | C =>
      refine ⟨m + 1, s - δ, by simp only [List.length_cons]; omega, ?_⟩
      have hev := sweepOperator_shiftAux_appendHeights_C (q := q) (u := u) hq hz hw hN hlowx
        (by omega) hevx hgaux hgpx Y
      rw [hδx] at hev
      rw [hLc, heq, map_smul,
        sweepOperator_stairWord_C (htyp.trans hevx) hbB, hev, map_smul,
        stairWord_succ_shift_zero_apply, hRc, smul_smul, ← zpow_add₀ hq]
      congr 2
    | D =>
      refine ⟨m, s + δ, by simp only [List.length_cons]; omega, ?_⟩
      have hev := sweepOperator_shiftAux_appendHeights_D (q := q) (u := u) hz hw hN hlowx hevx g Y
      rw [hδx] at hev
      rw [hLc, heq, map_smul, sweepOperator_stairWord_D (htyp.trans hevx), hev, map_smul,
        hRc, smul_smul, ← zpow_natCast q δ, ← zpow_add₀ hq]
    | E =>
      refine ⟨m, s, by simp only [List.length_cons]; omega, ?_⟩
      have hev := sweepOperator_shiftAux_appendHeights_E (q := q) (u := u) (z := z) (w := w)
        (by omega) hevx g Y
      rw [hδx] at hev
      rw [hLc, heq, map_smul, sweepOperator_stairWord_E (htyp.trans hevx), hev, hRc]

end Layer

end HJO.Mellit

end
