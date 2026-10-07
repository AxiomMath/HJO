/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepTailLayer
public import HJO.Shuffle.SweepLayerWidth
public meta import HJO.Attr

/-!
# The round boundary: the tail layer passes the staircase the base layer left

Two layers of a round of an extension are computed. `HJO.Mellit.exists_baseRound_shiftAux` turns the
**base** layer of round `e` into the base's own `HJO.Mellit.roundSweepWord`, at the price of a power
of `q` and a **staircase** `S_{0,m_e} = HJO.Sweep.stairWord q δ_e 0 m_e`;
`HJO.Mellit.tailRoundWord_appendHeights` turns the **tail** layer of round `e` into the tail's own
round word with every operator read at the single raised index `k^w(p) + β_e`,
`β_e = #(HJO.Paths.baseLiveSteps z e)`.

Since `HJO.Mellit.bandSweepWord_eq_prod_roundSweepWord` groups the band word as
`Round_0 · Round_1 ⋯ Round_D` with the highest excess applied first, and
`HJO.Mellit.roundSweepWord_split_fst` puts the tail layer of a round rightmost, the band word
applied to a vector is

`BL_0 · TL_0 · BL_1 · TL_1 ⋯ BL_D · TL_D`

read right to left. So between the base layer of round `e` and the tail layer of round `e-1` stands
exactly one commutation: **the tail layer of round `e-1` has to pass the staircase the base layer of
round `e` emitted.** That commutation is this file, and it is unavoidable — no route through the
round grouping can skip it.

## What passes, and at what price

`HJO.Sweep.dplus_stairWord`, `HJO.Sweep.dminus_stairWord` and `HJO.Sweep.corner_stairWord` pass a
staircase at a general offset provided the staircase's top letter stays inside the long word of the
operator. Raised to `HJO.Mellit.sweepOperatorShifted` this is
`HJO.Mellit.sweepOperatorShifted_stairWord_A`…`_E`, and along a whole list it is
`HJO.Mellit.layerWordShifted_stairWord`: the staircase comes out unchanged in `δ` and in `m`, with
its **offset raised by the number of type-`A`-or-`C` events of the list**
(`HJO.Mellit.acCount`) — the same bookkeeping the base layer's own induction does, and for the same
reason.

The price is a side condition, and it is stated rather than hidden: at every point `p` of the tail
layer the arriving staircase's top letter `c + m + δ - 1` must sit below the index
`k^w(p) + β` at which the tail's operator is read (one lower still at rules `B` and `C`, whose long
words are one letter shorter). Written out that is

`c + m + δ + 1 ≤ HJO.Paths.sweepWidth w p + β`.

**This is a genuine obligation and it is the round-boundary mirror of the layer's own width
condition.** Unlike that one it is *not* discharged here: the base layer's condition compares two
counts inside one rectangle and `HJO.Mellit.acCount_le_sweepRight` settles it by an injection of the
layer's type-`A`-or-`C` events into the live steps to the right; this one compares the base's
`m_e` and the tail's `δ_e` at level `e` with the tail's width and the base's `β_{e-1}` at level
`e-1`, so it couples the two rectangles across a round. It carries `a` through
`HJO.Paths.mem_tailLiveSteps_iff_Ioc` — a north step is live for exactly `a` consecutive levels —
and `a` enters the band identity nowhere else.

## What this does *not* do, and the obstruction that is left

Passing the staircase is the easy half of the round boundary. The hard half is the **block
order**, and it is worth recording precisely, because it is not a bookkeeping matter.

`HJO.Sweep.dplus_shiftAux_mul` and its siblings read a vector in the form `g·Σ_δF` with
`g ∈ HJO.Sweep.auxSubalg L ∩ HJO.Sweep.piece L δ`: the low block `y_1, …, y_δ` carries **no letter
of `Λ`**, and by `HJO.Sweep.exists_mul_shiftAux_of_monomial` every `y`-monomial of `V_{k+δ}` splits
that way with the `Λ`-coefficient going to the **high** block. So in the form the base layer
consumes, `Λ` is unavoidably high, and since the base's own word is what acts on the high block, the
high block is the base's. The `Λ`-freeness is not removable:
`HJO.Sweep.not_dplus_shiftAux_mul_of_mem_piece` below refutes the same statement with `hgaux`
dropped, so the mirror form — base low, tail high — is not available at all, and the `β_e`-versus-
`δ_e` mismatch cannot be repaired by re-blocking.

What is left is therefore: the tail's operators are read at the index `k^w(p) + β_e`, which is the
*total* grading, so they act at the top of the stack — on the high block, the base's. For the
reconciliation they must be recognised as the tail's own operators acting on the low block. The only
operators here that move one block past another are the staircases: reading the letters of
`HJO.Sweep.stairWord q δ c m` off `HJO.Sweep.stairWord_succ`, each block `T_{[c+i+1,c+i+δ]}` carries
the index `c+i+δ+1` down to `c+i+1`, so the underlying permutation of `S_{c,m}` is the transposition
of a block of `δ` with a block of `m`. (That is a reading of the word, not a statement proved here.)
Being positive braid words and not permutations, they do not perform the exchange as a relabelling,
and what the difference costs is the residual content of the band identity.

## One route is closed, and the obstruction is not a degeneracy

`HJO.Sweep.stairWord_succ_shift` folds a staircase whose offset has been raised back down only when
the fresh block carries the **same** `δ` — and `δ_e` is not constant across the rounds of one tail.
So from the second round boundary on, the accumulated correction is a *product* of staircases with
distinct `δ`, and each factor's offset keeps rising, by one per type-`A`-or-`C` event of every layer
it is carried across, while the grading does not rise with it.

On the smallest instance with `1 < a < b` and a genuine tail — `a = 2`, `b = 3`, `N = A = 1`, whose
two above-diagonal paths are `ŷ = (0,2,3)` and `ŷ = (0,3,3)` — every one of the four `(z, w)` pairs
has `δ_e ≠ β_e` at some round and `δ_e` non-constant (for `z = w = (0,2,3)` the shifts are
`0,0,1,2,2,1,0`), and on every one of the four the bound above **fails**: at `z = w = (0,3,3)` the
tail point `(2,5)` of round `4` is a type-`C` event of extension width `2`, and the staircase
arriving from the base layer of a higher round is `S_{0,1}` at `δ = 1`, whose single letter `T_1`
`HJO.Sweep.corner_stairWord` cannot carry past `Δ^{(2)}` — that lemma asks `c+m+δ+1 ≤ 2`, i.e.
`3 ≤ 2`.

Nor is that failure the harmless kind. A staircase all of whose letters sit **above** the current
grading is the identity, every letter fixing what `s_j` fixes
(`HJO.Sweep.braid_of_swapAux_eq`), so such a factor could simply be dropped; but here the offset is
`0` and the letter `T_1` is *inside* the grading `2`. The overlap is real, and no lemma of the
library covers it. So carrying the base layers' staircases outward across the following layers is
not a viable route to the reconciliation, and a different treatment of the correction is needed —
plausibly absorbing it into the two-block decomposition round by round rather than transporting it
as an operator.

## References

Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*, sections 4 and 6.
-/

@[expose] public section

namespace HJO.Mellit

open HJO.Sweep HJO.Paths Finset

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {a b N A : ℕ}

/-! ### The raised event operator, rule by rule -/

section Rules

variable {w : Heights a b A} {P : ℕ × ℕ}

/-- Rule `A` of `HJO.Mellit.sweepOperatorShifted` written out. -/
theorem sweepOperatorShifted_of_eventType_A (w : Heights a b A) (β : ℕ)
    (hP : eventType w P = EventType.A) :
    sweepOperatorShifted q u w P β = dplus q (sweepWidth w P + β) := by
  rw [sweepOperatorShifted, hP]

/-- Rule `B` of `HJO.Mellit.sweepOperatorShifted` written out. -/
theorem sweepOperatorShifted_of_eventType_B (w : Heights a b A) (β : ℕ)
    (hP : eventType w P = EventType.B) :
    sweepOperatorShifted q u w P β = dminus q (sweepWidth w P + β) := by
  rw [sweepOperatorShifted, hP]

/-- Rule `C` of `HJO.Mellit.sweepOperatorShifted` written out. Note the exponent is the tail's own,
unshifted, by `HJO.Paths.sweepRight_appendHeights_corner`. -/
theorem sweepOperatorShifted_of_eventType_C (w : Heights a b A) (β : ℕ)
    (hP : eventType w P = EventType.C) :
    sweepOperatorShifted q u w P β
      = q ^ (-(sweepRight w P : ℤ)) • corner q (sweepWidth w P + β) := by
  rw [sweepOperatorShifted, hP]

/-- Rule `D` of `HJO.Mellit.sweepOperatorShifted` written out: a scalar, reading no width. -/
theorem sweepOperatorShifted_of_eventType_D (w : Heights a b A) (β : ℕ)
    (hP : eventType w P = EventType.D) :
    sweepOperatorShifted q u w P β = q ^ sweepRight w P • (1 : Module.End L (Total L)) := by
  rw [sweepOperatorShifted, hP]

/-- Rule `E` of `HJO.Mellit.sweepOperatorShifted` written out: a scalar, reading no width. -/
theorem sweepOperatorShifted_of_eventType_E (w : Heights a b A) (β : ℕ)
    (hP : eventType w P = EventType.E) :
    sweepOperatorShifted q u w P β = u • (1 : Module.End L (Total L)) := by
  rw [sweepOperatorShifted, hP]

end Rules

/-! ### One raised event passes a staircase at a general offset -/

section OnePoint

variable {w : Heights a b A} {P : ℕ × ℕ}

/-- **Rule `A` at a raised index passes a staircase and raises its offset by one.** The bound is
`HJO.Sweep.dplus_stairWord`'s, read at the raised index `k^w(P) + β`. -/
theorem sweepOperatorShifted_stairWord_A (hA : eventType w P = EventType.A) {β δ c m : ℕ}
    (hm : c + m + δ ≤ sweepWidth w P + β) (X : Total L) :
    sweepOperatorShifted q u w P β (stairWord q δ c m X)
      = stairWord q δ (c + 1) m (sweepOperatorShifted q u w P β X) := by
  rw [sweepOperatorShifted_of_eventType_A w β hA]
  exact dplus_stairWord q m hm X

/-- **Rule `B` at a raised index passes a staircase unchanged.** One unit stronger than rule `A`'s
bound, `d^♭_-` reaching only the letters `T_j` with `j ≤ n - 2`. -/
theorem sweepOperatorShifted_stairWord_B (hB : eventType w P = EventType.B) {β δ c m : ℕ}
    (hm : c + m + δ + 1 ≤ sweepWidth w P + β) (X : Total L) :
    sweepOperatorShifted q u w P β (stairWord q δ c m X)
      = stairWord q δ c m (sweepOperatorShifted q u w P β X) := by
  rw [sweepOperatorShifted_of_eventType_B w β hB]
  exact dminus_stairWord q m hm X

/-- **Rule `C` at a raised index passes a staircase and raises its offset by one.** The `q`-exponent
is a scalar and commutes with everything. -/
theorem sweepOperatorShifted_stairWord_C (hC : eventType w P = EventType.C) {β δ c m : ℕ}
    (hm : c + m + δ + 1 ≤ sweepWidth w P + β) (X : Total L) :
    sweepOperatorShifted q u w P β (stairWord q δ c m X)
      = stairWord q δ (c + 1) m (sweepOperatorShifted q u w P β X) := by
  rw [sweepOperatorShifted_of_eventType_C w β hC]
  simp only [LinearMap.smul_apply]
  rw [corner_stairWord q m hm X, map_smul]

/-- **Rule `D` at a raised index passes a staircase unchanged**, being a scalar. No bound. -/
theorem sweepOperatorShifted_stairWord_D (hD : eventType w P = EventType.D) (β δ c m : ℕ)
    (X : Total L) :
    sweepOperatorShifted q u w P β (stairWord q δ c m X)
      = stairWord q δ c m (sweepOperatorShifted q u w P β X) := by
  rw [sweepOperatorShifted_of_eventType_D w β hD]
  simp only [LinearMap.smul_apply, Module.End.one_apply, map_smul]

/-- **Rule `E` at a raised index passes a staircase unchanged**, being a scalar. No bound. -/
theorem sweepOperatorShifted_stairWord_E (hE : eventType w P = EventType.E) (β δ c m : ℕ)
    (X : Total L) :
    sweepOperatorShifted q u w P β (stairWord q δ c m X)
      = stairWord q δ c m (sweepOperatorShifted q u w P β X) := by
  rw [sweepOperatorShifted_of_eventType_E w β hE]
  simp only [LinearMap.smul_apply, Module.End.one_apply, map_smul]

/-- **Every rule passes a staircase, the offset rising exactly at types `A` and `C`.** The five
rules merged into the shape the list induction consumes: the offset after the event is
`c + HJO.Mellit.acCount w [P]`, and the bound is the stronger of the two, which rules `A`, `D` and
`E` do not need. -/
theorem sweepOperatorShifted_stairWord (w : Heights a b A) {β δ c m : ℕ}
    (hm : c + m + δ + 1 ≤ sweepWidth w P + β) (X : Total L) :
    sweepOperatorShifted q u w P β (stairWord q δ c m X)
      = stairWord q δ (c + acCount w [P]) m (sweepOperatorShifted q u w P β X) := by
  cases hev : eventType w P with
  | A =>
    rw [acCount_cons_of_ac [] (Or.inl hev), acCount_nil]
    exact sweepOperatorShifted_stairWord_A hev (by omega) X
  | B =>
    rw [acCount_cons_of_not_ac [] (by simp [hev]), acCount_nil, Nat.add_zero]
    exact sweepOperatorShifted_stairWord_B hev hm X
  | C =>
    rw [acCount_cons_of_ac [] (Or.inr hev), acCount_nil]
    exact sweepOperatorShifted_stairWord_C hev hm X
  | D =>
    rw [acCount_cons_of_not_ac [] (by simp [hev]), acCount_nil, Nat.add_zero]
    exact sweepOperatorShifted_stairWord_D hev β δ c m X
  | E =>
    rw [acCount_cons_of_not_ac [] (by simp [hev]), acCount_nil, Nat.add_zero]
    exact sweepOperatorShifted_stairWord_E hev β δ c m X

end OnePoint

/-! ### The count of type-`A`-or-`C` events only grows -/

section Count

/-- Dropping the head of a list can only lower the count of its type-`A`-or-`C` events. -/
theorem acCount_le_cons (z : Heights a b N) (x : ℕ × ℕ) (ℓ : List (ℕ × ℕ)) :
    acCount z ℓ ≤ acCount z (x :: ℓ) := by
  by_cases hx : eventType z x = EventType.A ∨ eventType z x = EventType.C
  · rw [acCount_cons_of_ac ℓ hx]; omega
  · rw [acCount_cons_of_not_ac ℓ hx]

end Count

/-! ### A WHOLE RAISED LAYER PASSES A STAIRCASE -/

/-- **THE TAIL LAYER PASSES THE STAIRCASE, WITH ITS OFFSET RAISED BY THE LAYER'S OWN
TYPE-`A`-OR-`C` COUNT.** For a list `ℓ` of points of the tail's rectangle, read at a width raised by
the single integer `β` — which by `HJO.Mellit.tailRoundWord_appendHeights` is what the tail layer of
a round of an extension is —

`(∏_{p ∈ ℓ} O^{β}_p)(S_{c,m}X) = S_{c + #AC(ℓ), m}((∏_{p ∈ ℓ} O^{β}_p)X)`.

Neither `δ` nor the height `m` moves: a staircase is *carried* across a layer, not consumed by it.
Only the offset moves, and it moves by exactly what `HJO.Sweep.stairWord_succ_shift` would have to
undo — so the two layers of a round emit and absorb the same bookkeeping, which is the first thing
one would want to know about the round boundary.

The side condition is the one named in the module docstring, stated uniformly over the layer and
with the layer's **total** count rather than each suffix's, which is what makes it checkable against
the geometry: `c + #AC(ℓ) + m + δ + 1 ≤ k^w(p) + β` at every point. Rules `A`, `D` and `E` need
less; rules `B` and `C` need exactly this.

Nothing is assumed of `q`, of `u`, of `a` or of the two paths: this is the operator half of the
round boundary and it is hypothesis-free. What is *not* here is the block order — see the module
docstring. -/
@[hjo "lem_sweep_round_stair_pass"]
theorem layerWordShifted_stairWord (q u : L) (w : Heights a b A) (β δ m : ℕ) :
    ∀ (ℓ : List (ℕ × ℕ)) (c : ℕ),
      (∀ p ∈ ℓ, c + acCount w ℓ + m + δ + 1 ≤ sweepWidth w p + β) → ∀ X : Total L,
        (ℓ.map (fun p => sweepOperatorShifted q u w p β)).prod (stairWord q δ c m X)
          = stairWord q δ (c + acCount w ℓ) m
              ((ℓ.map (fun p => sweepOperatorShifted q u w p β)).prod X) := by
  intro ℓ
  induction ℓ with
  | nil => intro c _ X; simp
  | cons x t ih =>
    intro c hbd X
    have hmono : acCount w t ≤ acCount w (x :: t) := acCount_le_cons w x t
    have hbdt : ∀ p ∈ t, c + acCount w t + m + δ + 1 ≤ sweepWidth w p + β := by
      intro p hp
      have := hbd p (List.mem_cons_of_mem _ hp)
      omega
    have hbdx : c + acCount w t + m + δ + 1 ≤ sweepWidth w x + β := by
      have := hbd x (List.mem_cons_self ..)
      omega
    have hcons : ∀ Y : Total L,
        ((x :: t).map (fun p => sweepOperatorShifted q u w p β)).prod Y
          = sweepOperatorShifted q u w x β
              ((t.map (fun p => sweepOperatorShifted q u w p β)).prod Y) := by
      intro Y; rw [List.map_cons, List.prod_cons]; rfl
    rw [hcons, ih c hbdt X, sweepOperatorShifted_stairWord (P := x) w hbdx, hcons]
    congr 2
    by_cases hx : eventType w x = EventType.A ∨ eventType w x = EventType.C
    · rw [acCount_cons_of_ac t hx, acCount_cons_of_ac [] hx, acCount_nil]; omega
    · rw [acCount_cons_of_not_ac t hx, acCount_cons_of_not_ac [] hx, acCount_nil]
      omega

/-! ### The tail layer of a round of an extension passes the staircase -/

section Round

variable {z : Heights a b N} {w : Heights a b A}

/-- **THE ROUND BOUNDARY, OPERATOR HALF.** The tail layer of round `e` of an extension — the
extension's own operators at the round's points of corner abscissa, which
`HJO.Mellit.roundSweepWord_split_fst` puts rightmost in the round — carries a staircase across
unchanged but for its offset, which rises by the number of type-`A`-or-`C` events of the tail's own
round `e`.

This is `HJO.Mellit.tailRoundWord_appendHeights` composed with
`HJO.Mellit.layerWordShifted_stairWord`, and it is the commutation that stands between the base
layer of round `e+1` and the base layer of round `e`: the former emits
`S_{0,m_{e+1}}` by `HJO.Mellit.exists_baseRound_shiftAux`, and the latter can only be applied once
that staircase has been moved past the tail layer in between.

The side condition is the tail layer's, unchanged, and is the round-boundary width obligation. It is
the only hypothesis here that is not geometry already in hand. -/
@[hjo "lem_sweep_round_stair_pass"]
theorem tailRoundWord_stairWord (ha : 0 < a) (hN : 0 < N) (hA : 0 < A)
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) {η η'' : ℚ}
    (hη : SeparatesDiagonal a b (N + A) η) (hη'' : SeparatesDiagonal a b A η'') {e : ℤ}
    (he : 0 < e) (δ m c : ℕ)
    (hbd : ∀ p ∈ sortByRank a b A {p ∈ sweptAbove w η'' | diagExcess a b p = e},
      c + acCount w (sortByRank a b A {p ∈ sweptAbove w η'' | diagExcess a b p = e})
          + m + δ + 1 ≤ sweepWidth w p + #(baseLiveSteps z e))
    (X : Total L) :
    ((sortByRank a b (N + A) {P ∈ sweptAbove (appendHeights z w) η |
          diagExcess a b P = e ∧ a * N ≤ P.1}).map
        (sweepOperator q u (appendHeights z w))).prod (stairWord q δ c m X)
      = stairWord q δ
          (c + acCount w (sortByRank a b A {p ∈ sweptAbove w η'' | diagExcess a b p = e})) m
          (((sortByRank a b (N + A) {P ∈ sweptAbove (appendHeights z w) η |
                diagExcess a b P = e ∧ a * N ≤ P.1}).map
              (sweepOperator q u (appendHeights z w))).prod X) := by
  rw [tailRoundWord_appendHeights (q := q) (u := u) ha hN hA hz hw hη hη'' he]
  exact layerWordShifted_stairWord q u w (#(baseLiveSteps z e)) δ m _ c hbd X

end Round

end HJO.Mellit

/-! ### The low block cannot be the base's: `Λ`-freeness is not removable -/

namespace HJO.Sweep

section Refutation

variable {L : Type*} [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in
/-- `Σ_0` is the identity: the shift by nothing renames every variable to itself. -/
theorem shiftAux_zero_apply (F : Total L) : shiftAux L 0 F = F := by
  rw [shiftAux, show (fun x : ℕ => x + 0) = id from rfl, MvPolynomial.rename_id]
  rfl

omit [Algebra ℚ L] in
/-- **MEMBERSHIP IN THE GRADED PIECE IS NOT ENOUGH: `τ` DOES NOT FIX A LOW FACTOR THAT CARRIES
`Λ`.** `HJO.Sweep.qshift_of_mem_auxSubalg` fixes a low factor drawn from `HJO.Sweep.auxSubalg L` — a
`𝕜`-combination of `y`-monomials, no letter of the alphabet. Weakening that to
`g ∈ HJO.Sweep.piece L 1` makes the statement **false**: the power sum `p_1` lies in every graded
piece, being a constant, and `HJO.Sweep.qshift_powerSum` moves it by `(q-1)y_1`.

This is the one step of `HJO.Sweep.dplus_shiftAux_mul` that reads `hgaux`, and it fails at `δ = 1`,
so the failure is not an artefact of a degenerate shift. -/
@[hjo "not_sweep_low_block_lambda_free"]
theorem not_qshift_of_mem_piece {q : L} (hq : q ≠ 1) :
    ¬ ∀ g : Total L, g ∈ piece L 1 → qshift q 1 g = g := by
  intro h
  have hmem : (MvPolynomial.C (Sym.powerSum L 1) : Total L) ∈ piece L 1 := by
    rw [piece, MvPolynomial.mem_supported]; simp
  have key := h _ hmem
  have hpow := qshift_powerSum q 1 0 (L := L)
  rw [show (0 : ℕ) + 1 = 1 from rfl, pow_one, pow_one] at hpow
  have hz : scal (q - 1) * (auxVar 1 : Total L) = 0 := by linear_combination key - hpow
  refine absurd hz (mul_ne_zero ?_ ?_)
  · simp only [scal, ne_eq, MvPolynomial.C_eq_zero, sub_eq_zero]; exact hq
  · rw [auxVar]; exact MvPolynomial.X_ne_zero _

omit [Algebra ℚ L] in
/-- **THE MIRROR FORM IS NOT AVAILABLE: `d^♭_+` DOES NOT CARRY A LOW FACTOR THAT CARRIES `Λ`.**
`HJO.Sweep.dplus_shiftAux_mul` reads its low factor through
`HJO.Sweep.qshift_of_mem_auxSubalg`, which `HJO.Sweep.not_qshift_of_mem_piece` shows needs the
factor to carry no letter of `Λ`. With `hgaux` dropped and only `g ∈ HJO.Sweep.piece L δ` kept the
conclusion itself is false, and the witness below is at `δ = 0`, where the statement reads
`d^♭_+{}^{(k)}(gF) = g·d^♭_+{}^{(k)}F` for `g ∈ Λ` — that is, that `d^♭_+` is `Λ`-linear. It is only
`𝕜`-linear; the discrepancy is exactly the `(q-1)y_1` that `τ_{1,1}` adds to `p_1`, which is the
same mechanism at every `δ`.

Why this matters for the round boundary, and not merely as a check on a hypothesis: by
`HJO.Sweep.exists_mul_shiftAux_of_monomial` every `y`-monomial of `V_{k+δ}` splits as a `Λ`-free low
factor times `Σ_δ` of a high factor carrying the `Λ`-coefficient. So in the form the base layer
consumes, the `Λ` is *necessarily* high, and the high block is therefore the base's — the base's own
word is what acts there. The mirror arrangement, base low and tail high, would need this refuted
statement with the base state as `g`, and the base state is exactly a vector with `Λ`-coefficients.
So the tail layer's index shift `β_e` cannot be turned into the base layer's `δ_e` by exchanging
which block is low; the exchange has to be performed by an operator, and the only operators in this
library that move one block past another are the staircases. -/
@[hjo "not_sweep_low_block_lambda_free"]
theorem not_dplus_shiftAux_mul_of_mem_piece {q : L} (hq : q ≠ 1) :
    ¬ ∀ (k δ : ℕ) (g F : Total L), g ∈ piece L δ →
        dplus q (k + δ) (g * shiftAux L δ F)
          = cmAscWord q 1 δ (g * shiftAux L δ (dplus q k F)) := by
  intro h
  set p : Total L := MvPolynomial.C (Sym.powerSum L 1) with hp
  have hmem : p ∈ piece L 0 := by
    rw [hp, piece, MvPolynomial.mem_supported]; simp
  have hq1 : qshift q 1 p = p + scal (q - 1) * auxVar 1 := by
    have hpow := qshift_powerSum q 1 0 (L := L)
    rw [hp]; simpa using hpow
  have hd0 : ∀ F : Total L, dplus q 0 F = -(auxVar 1 * qshift q 1 F) := by
    intro F; rw [dplus_eq_ascWord]; simp [cmAscWord_self_pred]
  have key := h 0 0 p 1 hmem
  rw [shiftAux_zero_apply, shiftAux_zero_apply, cmAscWord_self_pred, mul_one,
    hd0, hd0, map_one, mul_one, hq1] at key
  simp only [Module.End.one_apply] at key
  have hz : scal (q - 1) * (auxVar 1 : Total L) ^ 2 = 0 := by linear_combination -key
  refine absurd hz (mul_ne_zero ?_ (pow_ne_zero _ ?_))
  · simp only [scal, ne_eq, MvPolynomial.C_eq_zero, sub_eq_zero]; exact hq
  · rw [auxVar]; exact MvPolynomial.X_ne_zero _

end Refutation

end HJO.Sweep
