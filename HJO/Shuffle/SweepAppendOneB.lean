/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.CmCommutator
public import HJO.SweepBlocks.Transport
public import HJO.Shuffle.SweepAppendOneTwo

/-! # The `α = []`, `A = 1` instance of `HJO.Mellit.SweepAppend`, at every `b`

`HJO.Mellit.sweepAppend_nil_one_one_two` (`HJO/Shuffle/SweepAppendOneTwo.lean`) evaluates both
sides of the `append` field at `α = []`, `A = 1`, `(a,b) = (1,2)` and finds them equal at every
`q ≠ 1`. This file generalises that instance in `b` — all of `0 < b` at once — and in doing so
proves the closed form of the corner operator at width `1` that the generalisation needs, which is
of independent use: `HJO.Sweep.corner_one_auxVar_mul` says `Δ^{(1)}` acts on `y_1V_1` as
multiplication by `-y_1`.

## The corner operator at width `1` is multiplication by `-y_1`

`HJO/Shuffle/SweepAppendOneTwo.lean` computes `Δ^{(1)}(y_1) = -y_1^2` by hand, out of the two
composites `d_-^{(2)}d_+^{(1)}(y_1) = e_1y_1` and `d_+^{(0)}d_-^{(1)}(y_1) = e_1y_1 + (q-1)y_1^2`,
and records that `Δ^{(1)}(y_1^m) = -y_1^{m+1}` is what a general `b` would need. That general
statement is *not* another hand computation: it is `HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM`
read at `k = 1`, where the conjugating braid word is empty, and carried across the two conventions
by `HJO.Sweep.dplus_transport` and `HJO.Sweep.dminus_transport`. The numerator of `HJO.Sweep.corner`
is then `(1-q)y_1` on all of `Y_1(V_1) = y_1V_1`
(`HJO.Sweep.dminus_dplus_sub_dplus_dminus_transport_one`) and `(q-1)^{-1}` turns the `1-q` into the
sign. `HJO.Sweep.corner_one_auxVar_pow` is the `y_1^m` case, with `m = 0` given by
`HJO.Sweep.corner_one_one`.

## The `1 × b` sweep, without a rank listing

`HJO.Mellit.aboveReturnPaths 1 b 1 [1]` is the singleton `{HJO.Mellit.baseOne b}`
(`HJO.Mellit.aboveReturnPaths_one_b`) for the same reason as at `b = 2`: an above-diagonal path of
`HJO.Paths.Heights 1 b 1` has `ŷ_0 = 0` and `ŷ_1 = b` and there is nothing else to choose
(`HJO.Mellit.eq_baseOne`). Its swept points above `HJO.Mellit.sepLevel 1 1 = 3/2` are
`(0,1), …, (0,b)`, of ranks `2, 4, …, 2b`, and they are peeled one at a time by
`HJO.Mellit.partialSweepWord_eq_sweepOperator_mul`, so **no rank listing is ever computed** at any
`b`:

* `(0,b)` is a type-`A` event of width `0`, operator `d_+^{(0)}`;
* `(0,k)` for `1 ≤ k < b` is a type-`C` event of width `1` with `a_{P̂} = 0`, operator `Δ^{(1)}`.

Where `b = 2` could read the event data off by `decide`, here each is a lemma:
`HJO.Mellit.eventType_baseOne_of_lt`, `HJO.Mellit.liveSteps_baseOne_of_lt` — the level line through
`(0,k)` crosses exactly the north step with foot `(0,k)`, since the window `2i ≤ 2k < 2i+2` forces
`i = k` — and `HJO.Mellit.sweepRight_baseOne_of_lt`.

**The levels are placed at `2k + 3/2`, not between consecutive ranks.** The isolation hypothesis of
`HJO.Mellit.partialSweepWord_eq_sweepOperator_mul` is about every lattice point of the rectangle,
not only the swept ones, and the odd ranks `2(y-b)+1 ≤ 1` of the column `x = 1` are in the way: the
window `(2k - 3/2, 2k + 1/2)` between two consecutive half-integer levels contains the integer
`2k-1`, which is a rank when `k = 1`. The window `(2k - 1/2, 2k + 3/2)` contains `2k` and `2k+1`
instead, and `2k+1 ≥ 3` is never a rank. That is what makes the induction uniform in `k`
(`HJO.Mellit.partialSweepWord_baseOne_step`); the `b = 2` file had to dispose of the same obstacle
by hand, as `HJO.Mellit.pointRank_ne_three`.

So `HJO.Mellit.dsc_one_b_eq` — unconditional in `q`, like `HJO.Mellit.dsc_one_two_eq` — and then
`HJO.Mellit.dsc_one_b_eq_neg_pow`: `D_{3/2,c_{(1)}} = (-y_1)^b` for `q ≠ 1`, which is exactly the
value `HJO.Mellit.stageTotal_one_left` gives the other side.

## How far this reaches, and why it stops there

`HJO.Mellit.sweepAppend_nil_one_one_b` is `α = []`, `A = 1`, `a = 1`, **every** `b > 0`, every
`q ≠ 1`. It does **not** reach the `hzero` hypothesis of
`HJO.Mellit.sweepAppend_of_forall_band`, which is `α = []` at every `A > 0` and every coprime
`0 < a < b`, and the obstruction is measured rather than guessed: the singleton path set that lets
the word be peeled is a singleton at exactly these parameters.

* `HJO.Mellit.one_lt_card_aboveReturnPaths_two_three_one` — at `(a,b) = (2,3)`, `A = 1` the set has
  the two paths `(0,2,3)` and `(0,3,3)`.
* `HJO.Mellit.one_lt_card_aboveReturnPaths_one_two_two` — at `(a,b) = (1,2)`, `A = 2` it has the two
  paths `HJO.Paths.tailEx1` and `HJO.Paths.tailEx2`.

**Both of those points are settled**, each by evaluating the two words and adding:
`HJO.Mellit.sweepAppend_nil_two_three_one` (`HJO/Shuffle/SweepAppendTwoThree.lean`) and
`HJO.Mellit.sweepAppend_nil_one_two_two` (`HJO/Shuffle/SweepAppendNilTwo.lean`). So the
singleton boundary is crossed in both directions and neither point is an obstruction.

Both ways out of the corner face a genuine sum over a rational Catalan set. That sum is **not** the
content of `HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc`; the comparison goes
through `HJO.Mellit.Rem41` (`HJO/Shuffle/Mellit.lean`), an identity in `𝒫` whose right-hand side is
`u^{N-ℓ} • ι(proj(d_-^ℓ(D_{η,c_α})))`, so it constrains only the image of the invariant under
`ι ∘ proj ∘ d_-^ℓ`, and the `proj` of `HJO.Mellit.sweepWitness` is `MvPolynomial.lcoeff _ 0`. It
also runs the other way: `HJO.Mellit.rem41_of_sweepComputes` reads the character sum *off* the word
sum, consuming `HJO.Mellit.dsc_compColouring_eq_sum_partialSweepWord`, and it mentions no
replication family and no `HJO.Mellit.stageTotal`. The statement whose content this sum is, is
`HJO.Mellit.mellitInduction_sweepWitness`, to which the `append` field is equivalent at the witness
by `HJO.Mellit.mellitInduction_sweepWitness_iff_sweepAppend`;
`HJO/Shuffle/SweepAppendNilDegenerate.lean` sets the verdict out in full.

The remark below is *not* the grading obstruction
that `HJO/Collinear/CommutationTheorem.lean` records against the termwise route: nothing here
compares an extended path with its truncation, the `α = []` case having no base path to truncate to.
It is the plainer fact that the `α = []` identity is a statement about a sum of many words as soon
as either parameter moves.
-/

@[expose] public section

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q : L}

/-! ### The corner operator at width `1`, in closed form -/

omit [Algebra ℚ L] in
/-- `Y_1 = -y_1`: the transport scalar of `HJO.Sweep.transport` at index `1`. -/
theorem transportScalar_one : transportScalar L 1 = -(auxVar 1 : Total L) := by
  rw [transportScalar_succ, transportScalar_zero, one_mul]

/-- **The numerator of `HJO.Sweep.corner` at width `1`, on the transport of an element of `V_1`.**
This is `HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` read at `k = 1`, where the conjugating
word is empty, carried from the Carlsson--Mellit pair of generators to the sweep pair by
`HJO.Sweep.dplus_transport` and `HJO.Sweep.dminus_transport`:
`(d_-d_+ - d_+d_-)(Y_1F) = (1-q)y_1Y_1F` for `F ∈ V_1`. -/
theorem dminus_dplus_sub_dplus_dminus_transport_one (q : L) {F : Total L} (hF : F ∈ piece L 1) :
    dminus q 2 (dplus q 1 (transport L 1 F)) - dplus q 0 (dminus q 1 (transport L 1 F))
      = scal (1 - q) * ((auxVar 1 : Total L) * transport L 1 F) := by
  have hword : cmAscWord q 1 0 = (1 : Module.End L (Total L)) := by
    rw [cmAscWord, Mellit.trainUpEnd_one_one]
  have hcom := dminusCM_cmDPlus_sub_cmDPlus_dminusCM q 0 hF
  rw [hword, Module.End.one_apply] at hcom
  have hL : dminus q 2 (dplus q 1 (transport L 1 F))
      = transport L 1 (dminusCM q 2 (cmDPlus q 1 F)) := by
    rw [dplus_transport q 1 F, dminus_transport q 1 (cmDPlus q 1 F)]
  have hR : dplus q 0 (dminus q 1 (transport L 1 F))
      = transport L 1 (cmDPlus q 0 (dminusCM q 1 F)) := by
    rw [dminus_transport q 0 F, dplus_transport q 0 (dminusCM q 1 F)]
  rw [hL, hR, ← map_sub, hcom, transport_apply, transport_apply]
  ring

/-- **`Δ^{(1)}(Y_1F) = -y_1Y_1F` for `F ∈ V_1`**, for every `q ≠ 1`: the corner operator at width
`1` acts on the transport of `V_1` as multiplication by `-y_1`. Dividing the numerator of
`HJO.Sweep.corner` by `q - 1` turns the `1 - q` of `HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM`
into the sign. -/
theorem corner_one_transport (hq : q ≠ 1) {F : Total L} (hF : F ∈ piece L 1) :
    corner q 1 (transport L 1 F) = -((auxVar 1 : Total L) * transport L 1 F) := by
  have hscal : (q - 1)⁻¹ * (1 - q) = -1 := by
    have hq' : q - 1 ≠ 0 := sub_ne_zero.2 hq
    field_simp
    ring
  rw [corner_of_pos q one_ne_zero, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.mul_apply, Module.End.mul_apply, show (1 : ℕ) + 1 = 2 from rfl,
    show (1 : ℕ) - 1 = 0 from rfl, dminus_dplus_sub_dplus_dminus_transport_one q hF,
    ← smul_eq_scal_mul, smul_smul, hscal, neg_one_smul]

/-- **`Δ^{(1)}(y_1F) = -y_1^2F` for `F ∈ V_1`**, for every `q ≠ 1`: `HJO.Sweep.corner_one_transport`
with the sign of the transport scalar absorbed into `F`. -/
theorem corner_one_auxVar_mul (hq : q ≠ 1) {F : Total L} (hF : F ∈ piece L 1) :
    corner q 1 ((auxVar 1 : Total L) * F)
      = -((auxVar 1 : Total L) * ((auxVar 1 : Total L) * F)) := by
  have hT : transport L 1 (-F) = (auxVar 1 : Total L) * F := by
    rw [transport_apply, transportScalar_one]
    ring
  have h := corner_one_transport hq (neg_mem hF)
  rw [hT] at h
  exact h

/-- **`Δ^{(1)}(y_1^m) = -y_1^{m+1}` for every `m`**, at every `q ≠ 1`. The case `m = 0` is
`HJO.Sweep.corner_one_one` and the rest is `HJO.Sweep.corner_one_auxVar_mul`; this is the
statement the docstring of `HJO/Shuffle/SweepAppendOneTwo.lean` records
`HJO.Sweep.corner_one_X_zero` as the instance `m = 1` of. -/
theorem corner_one_auxVar_pow (hq : q ≠ 1) (m : ℕ) :
    corner q 1 ((auxVar 1 : Total L) ^ m) = -((auxVar 1 : Total L) ^ (m + 1)) := by
  match m with
  | 0 =>
    rw [pow_zero, pow_one]
    exact corner_one_one hq
  | (n + 1) =>
    have hF : ((auxVar 1 : Total L)) ^ n ∈ piece L 1 :=
      pow_mem (auxVar_mem_piece le_rfl le_rfl) n
    rw [pow_succ' (auxVar 1 : Total L) n, corner_one_auxVar_mul hq hF,
      ← pow_succ' (auxVar 1 : Total L) n, ← pow_succ' (auxVar 1 : Total L) (n + 1)]

end HJO.Sweep

namespace HJO.Mellit

open HJO.Sweep Paths

/-! ### The forced above-diagonal path of the `1 × b` rectangle -/

variable {b : ℕ}

/-- The above-diagonal path of the `1 × b` rectangle, heights `(0, b)`. The generalisation of
`HJO.Mellit.baseEx` in the second parameter. -/
def baseOne (b : ℕ) : Heights 1 b 1 := fun r => if (r : ℕ) = 0 then 0 else Fin.last (b * 1)

@[simp]
theorem ht_baseOne_zero : ht (baseOne b) 0 = 0 := by
  rw [ht]
  simp [baseOne]

theorem ht_baseOne_of_ne_zero {r : ℕ} (hr : r ≠ 0) : ht (baseOne b) r = b := by
  rw [ht]
  split
  · next h =>
    have hr1 : (⟨r, h⟩ : Fin (1 * 1 + 1)) = ⟨1, by omega⟩ := by
      apply Fin.val_injective
      simp only
      omega
    rw [baseOne, hr1]
    simp [Fin.last]
  · simp

theorem isAboveDiagonal_baseOne : IsAboveDiagonal (baseOne b) := by
  refine ⟨ht_baseOne_zero, ?_, ?_, ?_⟩
  · rw [show 1 * 1 = 1 from rfl, ht_baseOne_of_ne_zero one_ne_zero, Nat.mul_one]
  · intro r hr
    have : r = 0 := by omega
    subst this
    rw [ht_baseOne_zero]
    exact Nat.zero_le _
  · intro r hr
    have hr' : r = 0 ∨ r = 1 := by omega
    rcases hr' with rfl | rfl
    · simp
    · rw [ht_baseOne_of_ne_zero one_ne_zero, Nat.mul_one, one_mul]

theorem hasAboveReturns_baseOne : HasAboveReturns [1] (baseOne b) := by
  refine ⟨isAboveDiagonal_baseOne, by decide, by decide, fun k hk => ?_⟩
  rw [show ([1] : List ℕ).scanl (· + ·) 0 = [0, 1] from by simp [List.scanl_cons, List.scanl_nil]]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  have hk' : k = 0 ∨ k = 1 := by omega
  rcases hk' with rfl | rfl
  · simp
  · rw [Nat.mul_one, ht_baseOne_of_ne_zero one_ne_zero, Nat.mul_one]
    simp

/-- **The above-diagonal path of the `1 × b` rectangle is forced.** The generalisation of
`HJO.Mellit.eq_baseEx`: the two heights `ŷ_0 = 0` and `ŷ_1 = b` are both pinned by
`HJO.Paths.IsAboveDiagonal`, and `HJO.Paths.Heights 1 b 1` has nothing else in it. -/
theorem eq_baseOne {y : Heights 1 b 1} (hy : IsAboveDiagonal y) : y = baseOne b := by
  have h0 : ht y 0 = 0 := hy.1
  have h1 : ht y 1 = b := by
    have := hy.2.1
    rwa [show 1 * 1 = 1 from rfl, Nat.mul_one] at this
  funext r
  have hlt := r.isLt
  have hr : (r : ℕ) = 0 ∨ (r : ℕ) = 1 := by omega
  apply Fin.val_injective
  rw [← ht_coe y r, ← ht_coe (baseOne b) r]
  rcases hr with hr | hr <;> rw [hr]
  · rw [h0, ht_baseOne_zero]
  · rw [h1, ht_baseOne_of_ne_zero one_ne_zero]

/-- **The index set of the `1 × b` sum is the singleton `{baseOne b}`.** The generalisation of
`HJO.Mellit.aboveReturnPaths_one_two`. -/
theorem aboveReturnPaths_one_b : aboveReturnPaths 1 b 1 [1] = {baseOne b} :=
  Finset.eq_singleton_iff_unique_mem.2
    ⟨mem_aboveReturnPaths_iff.2 hasAboveReturns_baseOne,
      fun _ hy => eq_baseOne (mem_aboveReturnPaths_iff.1 hy).1⟩

/-! ### The events of that path, and their operators -/

/-- The above-diagonal rank in the `1 × b` rectangle: `rk̂(x, y) = 2(y - bx) + x`. -/
theorem abovePointRank_one_b (x y : ℕ) :
    ParkingFunctions.abovePointRank 1 b 1 x y = 2 * ((y : ℤ) - b * x) + x := by
  rw [ParkingFunctions.abovePointRank]
  push_cast
  ring

theorem pointRank_one_b_zero (k : ℕ) : pointRank 1 b 1 ((0, k) : ℕ × ℕ) = 2 * k := by
  rw [pointRank, abovePointRank_one_b]
  push_cast
  ring

theorem attackWindow_one_one : attackWindow 1 1 = 2 := rfl

/-- The column of the path is its swept region's only interesting part: `(0, k)` is swept as soon
as `k ≤ b`. -/
theorem mem_sweptRegion_baseOne {k : ℕ} (hk : k ≤ b) :
    ((0, k) : ℕ × ℕ) ∈ sweptRegion (baseOne b) := by
  refine mem_sweptRegion.2 ⟨by omega, by omega, ?_⟩
  rw [show ((0, k) : ℕ × ℕ).1 + 1 = 1 from rfl, ht_baseOne_of_ne_zero one_ne_zero]
  exact hk

/-- Every swept point of the `1 × b` path has ordinate at most `b`. -/
theorem snd_le_of_mem_sweptRegion_baseOne {P : ℕ × ℕ} (hP : P ∈ sweptRegion (baseOne b)) :
    P.1 ≤ 1 ∧ P.2 ≤ b := by
  have h := mem_sweptRegion.1 hP
  refine ⟨by omega, ?_⟩
  have h2 := h.2.2
  rwa [ht_baseOne_of_ne_zero (Nat.succ_ne_zero _)] at h2

/-- The north steps of the `1 × b` path are `(0, 0), …, (0, b-1)`. -/
theorem mem_northSteps_baseOne_iff {P : ℕ × ℕ} :
    P ∈ northSteps (baseOne b) ↔ P.1 = 0 ∧ P.2 < b := by
  rw [mem_northSteps_iff]
  constructor
  · rintro ⟨h1, _, h3⟩
    rw [ht_baseOne_of_ne_zero (Nat.succ_ne_zero _)] at h3
    exact ⟨by omega, h3⟩
  · rintro ⟨h1, h2⟩
    rw [h1]
    refine ⟨by omega, ?_, ?_⟩
    · rw [ht_baseOne_zero]; exact Nat.zero_le _
    · rw [ht_baseOne_of_ne_zero (Nat.succ_ne_zero _)]; exact h2

/-- **Membership in the live set at `(0, k)`**, with the rank window written out. The level line of
the rank through `(0, k)` has rank `2k` and the step with foot `(0, i)` has rank `2i`, so the window
`2i ≤ 2k < 2i + 2` forces `i = k`. -/
theorem mem_liveSteps_baseOne_iff {k : ℕ} {P : ℕ × ℕ} :
    P ∈ liveSteps (baseOne b) ((0, k) : ℕ × ℕ) ↔ P.1 = 0 ∧ P.2 = k ∧ k < b := by
  rw [liveSteps, Finset.mem_filter, mem_northSteps_baseOne_iff, attackWindow_one_one,
    abovePointRank_one_b, abovePointRank_one_b]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    rw [h1] at h3 h4
    push_cast at h3 h4
    exact ⟨h1, by omega, by omega⟩
  · rintro ⟨h1, h2, h3⟩
    rw [h1, h2]
    push_cast
    refine ⟨⟨?_, h3⟩, ?_, ?_⟩
    · trivial
    · omega
    · omega

theorem liveSteps_baseOne_of_lt {k : ℕ} (hk : k < b) :
    liveSteps (baseOne b) ((0, k) : ℕ × ℕ) = {((0, k) : ℕ × ℕ)} := by
  ext P
  rw [mem_liveSteps_baseOne_iff, Finset.mem_singleton, Prod.ext_iff]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hk⟩⟩

theorem liveSteps_baseOne_top : liveSteps (baseOne b) ((0, b) : ℕ × ℕ) = ∅ := by
  ext P
  rw [mem_liveSteps_baseOne_iff]
  simp

theorem sweepWidth_baseOne_of_lt {k : ℕ} (hk : k < b) :
    sweepWidth (baseOne b) ((0, k) : ℕ × ℕ) = 1 := by
  rw [sweepWidth, liveSteps_baseOne_of_lt hk, Finset.card_singleton]

theorem sweepWidth_baseOne_top : sweepWidth (baseOne b) ((0, b) : ℕ × ℕ) = 0 := by
  rw [sweepWidth, liveSteps_baseOne_top, Finset.card_empty]

theorem sweepRight_baseOne_of_lt {k : ℕ} (hk : k < b) :
    sweepRight (baseOne b) ((0, k) : ℕ × ℕ) = 0 := by
  rw [sweepRight, liveSteps_baseOne_of_lt hk]
  simp

theorem sweepRight_baseOne_top : sweepRight (baseOne b) ((0, b) : ℕ × ℕ) = 0 := by
  rw [sweepRight, liveSteps_baseOne_top]
  simp

theorem eventType_baseOne_of_lt {k : ℕ} (hk0 : 0 < k) (hkb : k < b) :
    eventType (baseOne b) ((0, k) : ℕ × ℕ) = EventType.C := by
  have h0 : ht (baseOne b) 0 = 0 := ht_baseOne_zero
  have h1 : ht (baseOne b) (0 + 1) = b := ht_baseOne_of_ne_zero one_ne_zero
  change (if k < ht (baseOne b) 0 then EventType.E
    else if ht (baseOne b) 0 < k then
      (if 0 + 1 ≤ 1 * 1 ∧ k < ht (baseOne b) (0 + 1) then EventType.C else EventType.A)
    else if 0 + 1 ≤ 1 * 1 ∧ k < ht (baseOne b) (0 + 1) then EventType.B
      else EventType.D) = EventType.C
  rw [h0, h1]
  split_ifs with h h' <;> first | rfl | omega

theorem eventType_baseOne_top (hb : 0 < b) :
    eventType (baseOne b) ((0, b) : ℕ × ℕ) = EventType.A := by
  have h0 : ht (baseOne b) 0 = 0 := ht_baseOne_zero
  have h1 : ht (baseOne b) (0 + 1) = b := ht_baseOne_of_ne_zero one_ne_zero
  change (if b < ht (baseOne b) 0 then EventType.E
    else if ht (baseOne b) 0 < b then
      (if 0 + 1 ≤ 1 * 1 ∧ b < ht (baseOne b) (0 + 1) then EventType.C else EventType.A)
    else if 0 + 1 ≤ 1 * 1 ∧ b < ht (baseOne b) (0 + 1) then EventType.B
      else EventType.D) = EventType.A
  rw [h0, h1]
  split_ifs with h h' <;> first | rfl | omega

section Operators

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- The event operator inside the column: a type-`C` event of width `1` with nothing live to the
right, so the corner operator `Δ^{(1)}` with no power of `q`. -/
theorem sweepOperator_baseOne_of_lt (q u : L) {k : ℕ} (hk0 : 0 < k) (hkb : k < b) :
    sweepOperator q u (baseOne b) ((0, k) : ℕ × ℕ) = corner q 1 := by
  rw [sweepOperator, eventType_baseOne_of_lt hk0 hkb, sweepWidth_baseOne_of_lt hkb,
    sweepRight_baseOne_of_lt hkb]
  norm_num

/-- The event operator at the top of the column: a type-`A` event of width `0`, so `d_+^{(0)}`. -/
theorem sweepOperator_baseOne_top (q u : L) (hb : 0 < b) :
    sweepOperator q u (baseOne b) ((0, b) : ℕ × ℕ) = dplus q 0 := by
  rw [sweepOperator, eventType_baseOne_top hb, sweepWidth_baseOne_top]

/-! ### The sweep word of that path, peeled one event at a time -/

/-- Above every rank of the `1 × b` rectangle the partial word is empty. -/
theorem partialSweepWord_baseOne_top (q u : L) :
    partialSweepWord q u (baseOne b) (2 * (b : ℚ) + 3 / 2) = 1 := by
  refine partialSweepWord_of_forall_le q u (baseOne b) _ fun P hP => ?_
  obtain ⟨h1, h2⟩ := snd_le_of_mem_sweptRegion_baseOne hP
  rw [pointRank, abovePointRank_one_b]
  have hP1 : (P.1 : ℤ) ≤ 1 := by exact_mod_cast h1
  have hP2 : (P.2 : ℤ) ≤ (b : ℤ) := by exact_mod_cast h2
  have hb0 : (0 : ℤ) ≤ (b : ℤ) * P.1 := by positivity
  have hle : 2 * ((P.2 : ℤ) - b * P.1) + P.1 ≤ 2 * (b : ℤ) + 1 := by linarith
  have hQ : ((2 * ((P.2 : ℤ) - b * P.1) + P.1 : ℤ) : ℚ) ≤ ((2 * (b : ℤ) + 1 : ℤ) : ℚ) := by
    exact_mod_cast hle
  push_cast at hQ ⊢
  linarith

/-- **Lowering the level by one event of the column.** The window
`(2k - 1/2, 2k + 3/2)` isolates the rank `2k` of `(0, k)`: the only other integer in it is `2k + 1`,
and the odd ranks of the rectangle are the ranks `2(y - b) + 1 ≤ 1` of the points of the column
`x = 1`, which `k ≥ 1` excludes. The window of width `2` between two *consecutive* levels
`2k ± 1/2` would not isolate anything, which is why the levels are placed at `2k + 3/2`. -/
theorem partialSweepWord_baseOne_step (q u : L) {k : ℕ} (hk0 : 0 < k) (hkb : k ≤ b) :
    partialSweepWord q u (baseOne b) (2 * (k : ℚ) - 1 / 2)
      = sweepOperator q u (baseOne b) ((0, k) : ℕ × ℕ)
        * partialSweepWord q u (baseOne b) (2 * (k : ℚ) + 3 / 2) := by
  refine partialSweepWord_eq_sweepOperator_mul q u one_pos (P := ((0, k) : ℕ × ℕ))
    (ηhi := 2 * (k : ℚ) + 3 / 2) ⟨2 * (k : ℤ) + 1, by push_cast; ring⟩ ?_ ?_ ?_
    (mem_sweptRegion_baseOne hkb)
  · rw [pointRank_one_b_zero]
    push_cast
    linarith
  · rw [pointRank_one_b_zero]
    push_cast
    linarith
  · intro Q hQ1 hQ2 hlo hup
    rw [pointRank, abovePointRank_one_b] at hlo hup
    rw [pointRank, abovePointRank_one_b, pointRank_one_b_zero]
    push_cast at hlo hup
    have hQ1' : Q.1 ≤ 1 := by omega
    have hQ2' : (Q.2 : ℤ) ≤ (b : ℤ) := by exact_mod_cast (by omega : Q.2 ≤ b)
    have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk0
    have hd1 : 2 * (k : ℤ) ≤ 2 * ((Q.2 : ℤ) - b * Q.1) + Q.1 := by
      by_contra hc
      have hle : 2 * ((Q.2 : ℤ) - b * Q.1) + Q.1 ≤ 2 * (k : ℤ) - 1 := by
        have := Int.lt_iff_add_one_le.1 (not_le.1 hc)
        linarith
      have hle' : ((2 * ((Q.2 : ℤ) - b * Q.1) + Q.1 : ℤ) : ℚ) ≤ ((2 * (k : ℤ) - 1 : ℤ) : ℚ) := by
        exact_mod_cast hle
      push_cast at hle'
      linarith
    have hd2 : 2 * ((Q.2 : ℤ) - b * Q.1) + Q.1 ≤ 2 * (k : ℤ) + 1 := by
      by_contra hc
      have hle : 2 * (k : ℤ) + 2 ≤ 2 * ((Q.2 : ℤ) - b * Q.1) + Q.1 := by
        have := Int.lt_iff_add_one_le.1 (not_le.1 hc)
        linarith
      have hle' : ((2 * (k : ℤ) + 2 : ℤ) : ℚ) ≤ ((2 * ((Q.2 : ℤ) - b * Q.1) + Q.1 : ℤ) : ℚ) := by
        exact_mod_cast hle
      push_cast at hle'
      linarith
    rcases (by omega : Q.1 = 0 ∨ Q.1 = 1) with h1 | h1
    · rw [h1] at hd1 hd2 ⊢
      simp only [Nat.cast_zero, mul_zero, sub_zero, add_zero] at hd1 hd2 ⊢
      omega
    · rw [h1] at hd1 hd2
      simp only [Nat.cast_one, mul_one] at hd1 hd2
      omega

/-- **The partial word of the `1 × b` path, `j + 1` events down from the top of the column**:
`Δ^{(1)j}d_+^{(0)}`. The first event crossed is the type-`A` event at the top of the column
(`HJO.Mellit.sweepOperator_baseOne_top`) and every later one is a type-`C` event of width `1`
(`HJO.Mellit.sweepOperator_baseOne_of_lt`), so no rank listing is ever computed. -/
theorem partialSweepWord_baseOne_aux (q u : L) :
    ∀ j : ℕ, j + 1 ≤ b →
      partialSweepWord q u (baseOne b) (2 * ((b - j : ℕ) : ℚ) - 1 / 2)
        = corner q 1 ^ j * dplus q 0 := by
  intro j
  induction j with
  | zero =>
    intro hb
    rw [Nat.sub_zero, partialSweepWord_baseOne_step q u (by omega) le_rfl,
      sweepOperator_baseOne_top q u (by omega), partialSweepWord_baseOne_top, pow_zero,
      mul_one, one_mul]
  | succ n ih =>
    intro hb
    have hk0 : 0 < b - (n + 1) := by omega
    have hcast : ((b - n : ℕ) : ℚ) = ((b - (n + 1) : ℕ) : ℚ) + 1 := by
      have h1 : ((b - n : ℕ) : ℤ) = ((b - (n + 1) : ℕ) : ℤ) + 1 := by omega
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) h1
    rw [partialSweepWord_baseOne_step q u hk0 (by omega),
      sweepOperator_baseOne_of_lt q u hk0 (by omega),
      show 2 * ((b - (n + 1) : ℕ) : ℚ) + 3 / 2 = 2 * ((b - n : ℕ) : ℚ) - 1 / 2 from by
        rw [hcast]; ring,
      ih (by omega), pow_succ', mul_assoc]

/-- **The partial word of the `1 × b` path at the separating level `HJO.Mellit.sepLevel 1 1`.**
`b - 1` corner events above one `d_+^{(0)}`; the case `b = 1` is the empty power. -/
theorem partialSweepWord_baseOne (q u : L) (hb : 0 < b) :
    partialSweepWord q u (baseOne b) (sepLevel 1 1) = corner q 1 ^ (b - 1) * dplus q 0 := by
  have hcast : ((b - (b - 1) : ℕ) : ℚ) = 1 := by
    have : b - (b - 1) = 1 := by omega
    rw [this, Nat.cast_one]
  have h := partialSweepWord_baseOne_aux q u (b - 1) (show b - 1 + 1 ≤ b by omega)
  rw [hcast] at h
  rw [show sepLevel 1 1 = 2 * (1 : ℚ) - 1 / 2 from by rw [sepLevel]; norm_num]
  exact h

/-! ### The invariant of the `1 × b` rectangle at `c_{(1)}` -/

/-- **`D_{3/2,c_{(1)}} = Δ^{(1)b-1}(d_+^{(0)}(1))` in the `1 × b` rectangle.** Unconditional in `q`;
the generalisation of `HJO.Mellit.dsc_one_two_eq` in the second parameter. -/
theorem dsc_one_b_eq (q u : L) (hb : 0 < b) :
    dsc q u 1 b 1 (sepLevel 1 1) (compColouring 1 b [1])
      = (corner q 1 ^ (b - 1)) (dplus q 0 (1 : Total L)) := by
  rw [dsc_compColouring_eq_sum_partialSweepWord q u (isAdmissibleLevel_sepLevel 1 1)
      (separatesDiagonal_sepLevel' 1 b 1) (Nat.coprime_one_left b) one_pos hb
      (by simp) (by simp),
    aboveReturnPaths_one_b, Finset.sum_singleton, partialSweepWord_baseOne q u hb,
    Module.End.mul_apply]

/-- `Δ^{(1)j}(y_1^m) = (-1)^jy_1^{m+j}`, from `HJO.Sweep.corner_one_auxVar_pow`. -/
theorem corner_one_pow_auxVar_pow (q : L) (hq : q ≠ 1) (j m : ℕ) :
    (corner q 1 ^ j) ((auxVar 1 : Total L) ^ m)
      = (-1 : Total L) ^ j * (auxVar 1 : Total L) ^ (m + j) := by
  induction j generalizing m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, corner_one_auxVar_pow hq, map_neg, ih,
      show m + 1 + n = m + (n + 1) from by omega, pow_succ]
    ring

/-- **The invariant of the `1 × b` rectangle at `c_{(1)}`, evaluated: `(-y_1)^b`**, for every
`q ≠ 1`. This is the value `HJO.Mellit.replOneTotal_one_left` predicts for the stage, so the two
sides of the `α = []`, `A = 1`, `a = 1` instance of `HJO.Mellit.SweepAppend` agree at every `b`. -/
theorem dsc_one_b_eq_neg_pow (q u : L) (hq : q ≠ 1) (hb : 0 < b) :
    dsc q u 1 b 1 (sepLevel 1 1) (compColouring 1 b [1])
      = (-(auxVar 1 : Total L)) ^ b := by
  have hX : dplus q 0 (1 : Total L) = -((auxVar 1 : Total L) ^ 1) := by
    rw [pow_one, dplus_zero_one]
    rfl
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  rw [dsc_one_b_eq q u hb, hX, map_neg, corner_one_pow_auxVar_pow q hq, Nat.add_sub_cancel,
    show 1 + c = c + 1 from Nat.add_comm 1 c, neg_pow, pow_succ]
  ring

/-! ### The `α = []`, `A = 1`, `a = 1` instance of `HJO.Mellit.SweepAppend`, at every `b` -/

/-- **`HJO.Mellit.SweepAppend` at `α = []`, `A = 1`, `(a,b) = (1,b)`, verbatim, and it is TRUE for
every `q ≠ 1` and every `0 < b`.** Both sides are `(-y_1)^b`: the left by
`HJO.Mellit.dsc_one_b_eq_neg_pow` and the right by `HJO.Mellit.dsc_empty_eq_one` and
`HJO.Mellit.stageTotal_one_left`. The scalar `(-1)^{(a-1)A}(qu)^{1-A}` of the `append` field is `1`
here, so no sign is being hidden.

This is `HJO.Mellit.sweepAppend_nil_one_one_two` generalised in `b`, and nothing more: `A = 1` and
`a = 1` are both still fixed, and `HJO.Mellit.one_lt_card_aboveReturnPaths_one_two_two` and
`HJO.Mellit.one_lt_card_aboveReturnPaths_two_three_one` say why — the singleton path set that makes
this computation possible is a singleton at exactly these parameters. -/
theorem sweepAppend_nil_one_one_b (q u : L) (hq : q ≠ 1) (hb : 0 < b) :
    dsc q u 1 b (([] : List ℕ).sum + 1) (sepLevel 1 (([] : List ℕ).sum + 1))
        (compColouring 1 b ([] ++ [1]))
      = ((-1 : L) ^ ((1 - 1) * 1) * (q * u) ^ (1 - ((1 : ℕ) : ℤ))) •
          stageTotal q u 1 b ([] : List ℕ).length 1
            (dsc q u 1 b ([] : List ℕ).sum (sepLevel 1 ([] : List ℕ).sum)
              (compColouring 1 b ([] : List ℕ))) := by
  have hc : compColouring 1 b ([] : List ℕ) = (∅ : Finset (ℕ × ℕ)) := by simp [compColouring]
  have hone : dsc q u 1 b 0 (sepLevel 1 0) (compColouring 1 b ([] : List ℕ)) = (1 : Total L) := by
    rw [hc]
    exact dsc_empty_eq_one q u (isAdmissibleLevel_sepLevel 1 0)
      (separatesDiagonal_sepLevel' 1 b 0) (Nat.coprime_one_left b) one_pos hb
  simp only [List.sum_nil, List.length_nil, List.nil_append, Nat.zero_add]
  rw [hone, stageTotal_one_left q u hb, dsc_one_b_eq_neg_pow q u hq hb]
  norm_num

end Operators

/-! ### Where the singleton method stops

The whole computation above rests on `HJO.Mellit.aboveReturnPaths_one_b`: the index set of
`HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc`'s sum is one path, so there is
nothing to sum and the word can be peeled event by event. That is a coincidence of `a = 1` together
with `A = 1`, and it fails in *both* directions at the first opportunity. -/

/-- One of the two above-diagonal paths of the `2 × 3` rectangle with return composition `(1)`:
heights `(0, 2, 3)`. -/
def baseTwoThreeA : Heights 2 3 1 :=
  fun r => if (r : ℕ) = 0 then 0 else if (r : ℕ) = 1 then 2 else 3

/-- The other one: heights `(0, 3, 3)`. -/
def baseTwoThreeB : Heights 2 3 1 := fun r => if (r : ℕ) = 0 then 0 else 3

theorem hasAboveReturns_baseTwoThreeA : HasAboveReturns [1] baseTwoThreeA := by
  refine ⟨by decide, by decide, by decide, fun k hk => ?_⟩
  rw [show ([1] : List ℕ).scanl (· + ·) 0 = [0, 1] from by simp [List.scanl_cons, List.scanl_nil]]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  interval_cases k <;> decide

theorem hasAboveReturns_baseTwoThreeB : HasAboveReturns [1] baseTwoThreeB := by
  refine ⟨by decide, by decide, by decide, fun k hk => ?_⟩
  rw [show ([1] : List ℕ).scanl (· + ·) 0 = [0, 1] from by simp [List.scanl_cons, List.scanl_nil]]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  interval_cases k <;> decide

/-- **At `a = 2` the path set of the `α = []`, `A = 1` instance is already not a singleton.** The
`2 × 3` rectangle has two above-diagonal paths of return composition `(1)`, heights `(0,2,3)` and
`(0,3,3)`, so `HJO.Mellit.eq_baseOne` has no analogue at `a ≥ 2`: the `α = []` identity there is a
genuine sum over the rational Catalan set, not one word. -/
theorem one_lt_card_aboveReturnPaths_two_three_one : 1 < (aboveReturnPaths 2 3 1 [1]).card :=
  Finset.one_lt_card.2
    ⟨baseTwoThreeA, mem_aboveReturnPaths_iff.2 hasAboveReturns_baseTwoThreeA,
      baseTwoThreeB, mem_aboveReturnPaths_iff.2 hasAboveReturns_baseTwoThreeB, by decide⟩

/-- **At `A = 2` the path set of the `α = []` instance is already not a singleton either**, even at
`a = 1`: the `2 × 4` rectangle has the two above-diagonal paths `HJO.Paths.tailEx1` and
`HJO.Paths.tailEx2` of return composition `(2)`. So the method of
`HJO.Mellit.sweepAppend_nil_one_one_b` reaches exactly `a = 1`, `A = 1`, and each of the two ways
out of that corner runs into a sum. -/
theorem one_lt_card_aboveReturnPaths_one_two_two : 1 < (aboveReturnPaths 1 2 2 [2]).card :=
  Finset.one_lt_card.2
    ⟨tailEx1, mem_aboveReturnPaths_iff.2 hasAboveReturns_tailEx1,
      tailEx2, mem_aboveReturnPaths_iff.2 hasAboveReturns_tailEx2, by decide⟩

end HJO.Mellit

end
