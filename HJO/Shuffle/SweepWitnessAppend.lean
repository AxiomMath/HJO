/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepWitnessBraid
public import HJO.Shuffle.Euclid

/-! # The `append` field at the sweep witness is one identity about `HJO.Mellit.dsc`

`HJO.Mellit.MellitInduction` at `HJO.Mellit.sweepWitness` is equivalent to
`HJO.Mellit.BraidClosedForm` by `HJO.Mellit.mellitInduction_iff_braidClosedForm`, whose three
conjuncts are settled in `HJO/Shuffle/SweepWitnessBraid.lean` except for the `append` field of
`HJO.Mellit.IsBraidValue`. This file computes that field at the witness and finds it equivalent to
one identity about the sweep process, `HJO.Mellit.SweepAppend`:
`HJO.Mellit.mellitInduction_sweepWitness_iff_sweepAppend`.

## What the computation removes

`HJO.Mellit.braidRep_specialBraid_dplusIter` is a statement *about the braid representation*: its
two sides are `π_{k+1}(B_{s,w,β})d_+^{k+1}(1)` and a composite acting on `π_k(B_{s,v,α})d_+^k(1)`,
and its proof runs through `HJO.Sweep.braidRep`, `HJO.Braid.braidStep`,
`HJO.Braid.specialBraid_mul_trainDown_one`, `HJO.Sweep.braid_dplusIter`, `HJO.Sweep.dplus_dplusIter`
and `HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece`. At the witness none of that
vocabulary appears in the *statement* of the field, and this file shows none of it is needed to
state the residue either:

* the braid value is forced, and is `HJO.Mellit.dsc` in the grading `ℓ`
  (`HJO.Mellit.braidValue_eq_sweepIn`, off `HJO.Mellit.colourParts_compColouring` and
  `HJO.Mellit.colourMult_compColouring`);
* the operator `G_{ℓ+1,A}` of `HJO.Mellit.stage` acts degreewise, and its component on the grading
  `ℓ` is written out here as `HJO.Mellit.stageTotal` — a word in `HJO.Braid.trainDown`,
  `HJO.Braid.trainUp`, `HJO.Sweep.slopeOperator`, `HJO.Sweep.zop`, `HJO.Sweep.dplusStar` and
  multiplication by `y_1`, with no replication family left in it
  (`HJO.Mellit.sweepWitness_stage_sweepIn`).

The second point is what `HJO.Mellit.euclid` buys, and it is spent here exactly where the
proof of `HJO.Mellit.braidRep_specialBraid_dplusIter` spends it: `Ω(1;1,1) = -y_1d^*_+` and
`Ω(2;1,1) = -y_1z_1` are `HJO.Mellit.IsReplicationFamily` at the Stern–Brocot parent pair `(0,1)`
with complement `(1,0)` (`HJO.Mellit.omega_one_one_one`, `HJO.Mellit.omega_two_one_one`), and
`HJO.Mellit.euclid` at `j = 1` and `j = 2` turns those into `Ω(1;a,b)` and `Ω(2;a,b)` up to the
sign `(-1)^{a-1}`. The two occurrences of that sign are the only place the `(-1)^{(a-1)A}` of the
field comes from, and they are visible in `HJO.Mellit.replOneTotal` and
`HJO.Mellit.replTwoTotal`.

Since the formula for the stage is independent of which replication family is used — both of its
inputs are pinned by `HJO.Mellit.euclid` — every statement below quantifies over an arbitrary
`HJO.Mellit.IsReplicationFamily`, and nothing needs `HJO.Mellit.replFamily` to be named.

## The equivalence, not a reduction

`HJO.Mellit.braidClosedForm_sweepWitness_iff_sweepAppend` is an `iff`, and both halves are used:
read one way it is the reduction, read the other it certifies that nothing was smuggled in. The
backward half is available because the braid value is *forced* at this witness —
`HJO.Mellit.IsColouringValue` pins `B α` at every `α` with positive parts, the empty composition
included, and `HJO.Mellit.sweepWitness_D_compColouring_congr_level` says the level it is read at
does not matter.

## Corners

`HJO.Mellit.SweepAppend` carries the hypotheses the field carries and no others: `α` has positive
parts and `0 < A`. So `α = [0]` — where `HJO.Mellit.colourParts_compColouring_zero_part` refutes the
witness's `colourParts` convention — is out of range, while `α = []` with `0 < A` is *in* range and
is the first step off the `nil` field: there the right-hand side reads
`HJO.Mellit.dsc q u a b 0 (1/2) ∅`, which is `1` by `HJO.Mellit.dsc_empty_eq_one`, so the identity
at `α = []` says `D_{η,c_{(A)}} = (-1)^{(a-1)A}(qu)^{1-A}G_{1,A}(1)`. At `A = 1` the power
`(Z^{(k+1)}_{a,b})^{A-1}` is the identity and the two signs `(-1)^{(a-1)A}` and `(-1)^{a-1}` cancel.
Nothing here needs `1 < a`: `0 < a`, `0 < b` and coprimality are all that is spent, which is why
`a = 1` is not a corner.

## Implementation notes

`HJO.Mellit.sweepWitness` has `W := HJO.Mellit.Graded L`, but the two types are equal only up to
unfolding the structure instance, so a goal mixing `HJO.Mellit.gradedIn` with a field of the witness
is type-correct while `rw` refuses to match inside it. `HJO.Mellit.sweepIn` is that same map with
its target read as `(HJO.Mellit.sweepWitness q u a b).W`, and every statement below uses it; the
three general plumbing lemmas are stated over an arbitrary module and an arbitrary injection, which
is what lets them apply on either reading.

## `HJO.Mellit.SweepAppend` IS FALSE, and so is this `iff`'s other side

`HJO.Mellit.not_sweepAppend_one_left` (`HJO/Shuffle/SweepAppendRefuted.lean`) refutes
`HJO.Mellit.SweepAppend` at `q = 1`, `a = 1`, every `1 < b`, and transports the refutation along
the two equivalences of this file to `HJO.Mellit.BraidClosedForm` and
`HJO.Mellit.MellitInduction` at the sweep witness. `HJO.Sweep.corner` is `(q-1)^{-1}` times a
difference of composites, so at `q = 1` it is the **zero map**, and the event operator of
`HJO.Mellit.sweepOperator` at a type-`C` event is a scalar multiple of it; one such event above the
level annihilates the whole `List.prod`. The one-part composition `(1)` puts such an event
on *every* path whenever `a < b` (`HJO.Mellit.dsc_one_eq_zero`), so the left side vanishes while the
right side is `(-y_1)^b ≠ 0`.

So nothing below is a proof obligation as stated. The target is
`HJO.Mellit.shuffle_of_lhs_and_induction`'s *quantified* clause, which asks for
`HJO.Mellit.MellitInduction` only at `q, u` algebraically independent over `ℤ` and at `1 < a < b` —
`q = 1` and `a = 1` are both excluded there, so the shuffle side is untouched. Anything proved from
the residue below must therefore carry `q ≠ 1` (or the algebraic independence), and the `iff`s of
this file have to be restated at a generic `q` before they can carry it.

`HJO.Mellit.sweepAppend_nil_one_one_two` (`HJO/Shuffle/SweepAppendOneTwo.lean`) localises the
defect to exactly that: at `(a,b) = (1,2)`, `α = []`, `A = 1` both sides are evaluated against the
sweep process and found **equal for every `q ≠ 1`**. So the sign `(-1)^{(a-1)A}`, the scalar
`(qu)^{1-A}`, `HJO.Mellit.sepLevel` and `HJO.Mellit.stageTotal` are all confirmed; the missing
hypothesis is the whole of what is wrong at that instance.

## What remains

`HJO.Mellit.SweepAppend` at a generic `q`, the one thing between the shuffle side and
`HJO.Mellit.MellitInduction`. Three readings of it are recorded:

* `HJO.Mellit.sweepAppend_iff_sum` — the identity between two sums of partial sweep words, indexed
  by `HJO.Mellit.aboveReturnPaths` (`HJO.Mellit.dsc_compColouring_eq_sum_partialSweepWord`), with
  no level in either index set (`HJO.Mellit.sweptAbove_eq_filter`);
* `HJO.Mellit.dsc_singleton_of_sweepAppend` — the `α = []` instance in closed form,
  `D_{η,c_{(A)}} = (-1)^{(a-1)A}(qu)^{1-A}Ω(2;a,b)^{A-1}Ω(1;a,b)(1)`, the base case;
* `HJO.Mellit.dsc_append_one_of_sweepAppend` — the `A = 1` instance, which is sign-free.

It is not vacuous: `HJO.Mellit.stageTotal_one_left_ne_zero` computes the stage on the vacuum at
`(a,b) = (1,b)` and finds `(-y_1)^b ≠ 0`, which is the check the three `shape_*` fields of
`HJO.Mellit.SweepSystem` cannot make — the zero operator satisfies all three.

The two sums are indexed by paths of *different* rectangles, `a(N+A) × b(N+A)` on the left and
`aN × bN` on the right, and `HJO.ParkingFunctions.abovePointRank` carries the rectangle. One half of
that is settled here and one half is not. `HJO.Mellit.abovePointRank_le_congr`: the rank *order* on
a shared pair of points is the same in both rectangles, so the two `HJO.Mellit.sortByRank` listings
agree and the rank normalisation is no obstruction. The other half is the comparison of the *paths*,
and it is supplied in `HJO/Shuffle/SweepTruncate.lean` and `HJO/Shuffle/SweepAppendWidth.lean`,
which import this file. Those two files provide:

* the truncation of an above-diagonal path of return composition `α ++ (A)` to one of composition
  `α`, and the extension inverse to it — `HJO.Paths.truncHeights`, `HJO.Paths.tailHeights`,
  `HJO.Paths.appendHeights`, with the transfers of `HJO.Paths.HasAboveReturns`;
* the fibres of that truncation — `HJO.Mellit.sum_aboveReturnPaths_append_singleton`: the sum over
  the big index set is a double sum whose inner index set is `aboveReturnPaths a b A (A)`
  *independently of the outer index*, so the fibre is one and the same set of tails;
* the comparison at a shared point of `HJO.Paths.sweepWidth`, `HJO.Paths.sweepRight` and the event
  type of `HJO.Mellit.sweepOperator` — `HJO.Paths.eventType_appendHeights` (unchanged),
  `HJO.Paths.sweepWidth_appendHeights` and `HJO.Paths.sweepRight_appendHeights` (shifted by the
  number of live north steps the extension adds at columns `≥ aN`);
* the shift in closed form — `HJO.Paths.liveSteps_high_appendHeights`, with
  `HJO.Paths.card_liveSteps_high_appendHeights_ne` showing it is **not** constant across the fibre,
  so no factor pulled out of the inner sum can absorb it.

What the extension's north steps cost is therefore measured rather than guessed, and the measurement
is negative for the termwise reading: `HJO.Mellit.stageTotal_mem_piece` says the stage raises the
grading by exactly one however large `A` is, while the shift runs over a band, and types `A`, `B`,
`C` each have an explicit counter-witness in `HJO/Shuffle/SweepAppendWidth.lean` against
absorbing it by conjugation. What remains is `HJO.Mellit.sweepAppend_of_forall_band`: one
identity per base path inside the band `1 ≤ ay - bx ≤ a·bA`.
-/

@[expose] public section

namespace HJO.Mellit

open HJO.Sweep Paths

/-! ### Operators that act through an injection

Three general steps, stated for a module `W` and a map `ι : Total L → W` so that they apply both to
`HJO.Mellit.gradedIn` and to `HJO.Mellit.sweepIn`: an operator acting through `ι` by `g` survives a
power, a list product and the monoid evaluation of a slope word. Each is used at a grading the
operator preserves. -/

section Plumbing

variable {L : Type*} [CommRing L] {W : Type*} [AddCommGroup W] [Module L W]
  (ι : Total L →ₗ[L] W)

/-- **A power acts through `ι` by the corresponding power.** -/
theorem pow_apply_comm {Φ : Module.End L W} {g : Module.End L (Total L)}
    (h : ∀ F, Φ (ι F) = ι (g F)) (m : ℕ) (F : Total L) : (Φ ^ m) (ι F) = ι ((g ^ m) F) := by
  induction m generalizing F with
  | zero => simp
  | succ n ih => rw [pow_succ, Module.End.mul_apply, h, ih, pow_succ, Module.End.mul_apply]

/-- **A product along a list acts through `ι` by the corresponding product.** -/
theorem list_prod_apply_comm {ι' : Type*} {Φ : ι' → Module.End L W}
    {g : ι' → Module.End L (Total L)}
    (h : ∀ (i : ι') (F : Total L), Φ i (ι F) = ι (g i F)) (ws : List ι') (F : Total L) :
    ((ws.map Φ).prod) (ι F) = ι ((ws.map g).prod F) := by
  induction ws with
  | nil => simp
  | cons i ws ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, h, List.map_cons, List.prod_cons,
      Module.End.mul_apply]

/-- **The slope word evaluated at two operators acting through `ι` acts through `ι`.**
`HJO.Mellit.slopeEval` is a product along `HJO.Mellit.slopeWord`, one factor per letter. -/
theorem slopeEval_apply_comm {Y Z : Module.End L W} {Y' Z' : Module.End L (Total L)}
    (hY : ∀ F, Y (ι F) = ι (Y' F)) (hZ : ∀ F, Z (ι F) = ι (Z' F)) (m n : ℕ) (F : Total L) :
    slopeEval Y Z m n (ι F) = ι (slopeEval Y' Z' m n F) := by
  rw [slopeEval, slopeEval]
  refine list_prod_apply_comm ι (fun l F => ?_) _ F
  cases l with
  | y => exact hY F
  | z => exact hZ F

end Plumbing

/-! ### The gradings of the witness, and its fields read on one of them

Each operator field of `HJO.Mellit.sweepWitness` is `HJO.Mellit.gradedOp` of the corresponding
`k`-indexed family, so each acts on one grading by one member of that family. The trains are read
at the index the grading forces, which is where `HJO.Mellit.trainDownFam`'s side condition
`1 ≤ j ∧ j ≤ m` is discharged: `HJO.Mellit.stage` applies `trainDown (k+1)` on the grading
`k+1`. -/

section Fields

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The `k`-th grading of the witness's total space.** `HJO.Mellit.gradedIn` with its target read
as `(HJO.Mellit.sweepWitness q u a b).W`, which is that type by unfolding the structure instance.
Stating the computations below through this map rather than through `HJO.Mellit.gradedIn` is what
lets `rw` see them; see the module docstring. -/
noncomputable def sweepIn (q u : L) (a b k : ℕ) : Total L →ₗ[L] (sweepWitness q u a b).W :=
  gradedIn L k

/-- **A grading is a direct summand.** Reading the `k`-th component back is a retraction, so an
identity between two elements of one grading is an identity in `HJO.Sweep.Total L`. This is what
makes the equivalences below equivalences. -/
theorem sweepIn_injective (q u : L) (a b k : ℕ) : Function.Injective (sweepIn q u a b k) := by
  intro F G h
  have h' : gradedIn L k F = gradedIn L k G := h
  have h'' := congrArg (DirectSum.component L ℕ (fun _ : ℕ => Total L) k) h'
  rwa [gradedIn, DirectSum.component.lof_self, DirectSum.component.lof_self] at h''

/-- The vacuum is the unit of the grading `0`. -/
theorem sweepIn_zero_one (q u : L) (a b : ℕ) :
    sweepIn q u a b 0 (1 : Total L) = (sweepWitness q u a b).vac := rfl

/-- Multiplication by `y_1` on a positive grading. -/
theorem sweepWitness_y1_sweepIn (q u : L) (a b k : ℕ) (F : Total L) :
    (sweepWitness q u a b).y1 (sweepIn q u a b (k + 1) F)
      = sweepIn q u a b (k + 1) (LinearMap.mulLeft L (auxVar 1 : Total L) F) := by
  change gradedOp (y1Fam L) id (gradedIn L (k + 1) F) = gradedIn L (k + 1) _
  rw [gradedOp_apply, y1Fam]
  rfl

/-- `z_1` of `HJO.Sweep.zop` on a positive grading. -/
theorem sweepWitness_z1_sweepIn (q u : L) (a b k : ℕ) (F : Total L) :
    (sweepWitness q u a b).z1 (sweepIn q u a b (k + 1) F)
      = sweepIn q u a b (k + 1) (zopOneStar q u (k + 1) F) := by
  change gradedOp (z1Fam q u) id (gradedIn L (k + 1) F) = gradedIn L (k + 1) _
  rw [gradedOp_apply, z1Fam]
  rfl

/-- `d^*_+` of `HJO.Sweep.dplusStar`, raising the grading by one. -/
theorem sweepWitness_dplusStar_sweepIn (q u : L) (a b k : ℕ) (F : Total L) :
    (sweepWitness q u a b).dplusStar (sweepIn q u a b k F)
      = sweepIn q u a b (k + 1) (dplusStar q u k F) := by
  change gradedOp (fun k => dplusStar q u k) (fun k => k + 1) (gradedIn L k F)
    = gradedIn L (k + 1) _
  rw [gradedOp_apply]

/-- `T_{k+1↘1}` of `HJO.Braid.trainDown`, read on the grading `k+1` it belongs to. -/
theorem sweepWitness_trainDown_sweepIn (q u : L) (a b k : ℕ) (F : Total L) :
    (sweepWitness q u a b).trainDown (k + 1) (sweepIn q u a b (k + 1) F)
      = sweepIn q u a b (k + 1) (trainDownEnd q (k + 1) 1 F) := by
  change gradedOp (trainDownFam q (k + 1)) id (gradedIn L (k + 1) F) = gradedIn L (k + 1) _
  rw [gradedOp_apply, trainDownFam, ite_eq_left (⟨by omega, le_rfl⟩ : 1 ≤ k + 1 ∧ k + 1 ≤ k + 1)]
  rfl

/-- `T_{1↗k+1}` of `HJO.Braid.trainUp`, read on the grading `k+1` it belongs to. -/
theorem sweepWitness_trainUp_sweepIn (q u : L) (a b k : ℕ) (F : Total L) :
    (sweepWitness q u a b).trainUp (k + 1) (sweepIn q u a b (k + 1) F)
      = sweepIn q u a b (k + 1) (trainUpEnd q 1 (k + 1) F) := by
  change gradedOp (trainUpFam q (k + 1)) id (gradedIn L (k + 1) F) = gradedIn L (k + 1) _
  rw [gradedOp_apply, trainUpFam, ite_eq_left (⟨by omega, le_rfl⟩ : 1 ≤ k + 1 ∧ k + 1 ≤ k + 1)]
  rfl

/-- **The slope operator `Ξ_{m,n}` of `HJO.Sweep.slopeOperator` acts degreewise**, by the member
of index `k+1` of the family `HJO.Sweep.slopeOperator`. Both substituted operators — `-y_1`
and `(qu)^{-1}z_1` — are degreewise and preserve the grading, so
`HJO.Mellit.slopeEval_apply_comm` applies letter by letter. -/
theorem sweepWitness_slopeEval_sweepIn (q u : L) (a b k m n : ℕ) (F : Total L) :
    slopeEval (-(sweepWitness q u a b).y1) ((q * u)⁻¹ • (sweepWitness q u a b).z1) m n
        (sweepIn q u a b (k + 1) F)
      = sweepIn q u a b (k + 1) (slopeOperator q u (k + 1) m n F) := by
  have hy : ∀ F : Total L, (-(sweepWitness q u a b).y1) (sweepIn q u a b (k + 1) F)
      = sweepIn q u a b (k + 1) ((-LinearMap.mulLeft L (auxVar 1 : Total L)) F) := by
    intro F
    rw [LinearMap.neg_apply, sweepWitness_y1_sweepIn, LinearMap.neg_apply, map_neg]
  have hz : ∀ F : Total L, ((q * u)⁻¹ • (sweepWitness q u a b).z1) (sweepIn q u a b (k + 1) F)
      = sweepIn q u a b (k + 1) (((q * u)⁻¹ • zop q u (k + 1) 1) F) := by
    intro F
    rw [LinearMap.smul_apply, sweepWitness_z1_sweepIn, LinearMap.smul_apply, map_smul, zop_one]
  rw [slopeOperator_eq_slopeEval]
  exact slopeEval_apply_comm _ hy hz m n F

end Fields

/-! ### The two replicated operators at `(a,b)`, with no replication family left in them

`HJO.Mellit.IsReplicationFamily` at `(1,1)` is two compositions of base values, and
`HJO.Mellit.euclid` carries them to `(a,b)`. These two lemmas are the whole of what the stage needs
from a replication family, and they are what make `HJO.Mellit.stageTotal` a word in the operators
of the sweep. -/

section Omega

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- **`Ω(1;1,1) = -y_1d^*_+`.** `HJO.Mellit.IsReplicationFamily`'s first rule at `(1,1)`, whose
Stern–Brocot parent pair is `(0,1)` with complement `(1,0)`. -/
theorem omega_one_one_one {S : SweepSystem L q u} {Ω : ℕ → ℕ → ℕ → (S.W →ₗ[L] S.W)}
    (hΩ : IsReplicationFamily S Ω) : Ω 1 1 1 = -(S.y1 ∘ₗ S.dplusStar) := by
  have hp : IsSBParent 1 1 0 1 := ⟨by omega, by omega, by norm_num⟩
  have h := hΩ.rule_one 1 1 0 1 (by norm_num) le_rfl le_rfl hp
  rw [hΩ.base_three, hΩ.base_one] at h
  simpa using h

/-- **`Ω(2;1,1) = -y_1z_1`.** `HJO.Mellit.IsReplicationFamily`'s second rule at `(1,1)`. -/
theorem omega_two_one_one {S : SweepSystem L q u} {Ω : ℕ → ℕ → ℕ → (S.W →ₗ[L] S.W)}
    (hΩ : IsReplicationFamily S Ω) : Ω 2 1 1 = -(S.y1 ∘ₗ S.z1) := by
  have hp : IsSBParent 1 1 0 1 := ⟨by omega, by omega, by norm_num⟩
  have h := hΩ.rule_two 1 1 0 1 (by norm_num) le_rfl le_rfl hp
  rw [hΩ.base_three, hΩ.base_two] at h
  simpa using h

/-- **`HJO.Mellit.euclid` read as a formula for `Ω(j;a,b)`.** The identity
`Ξ_{a,b}Ω(j;1,1) = (-1)^{a-1}Ω(j;a,b)` is inverted by multiplying by the sign, which squares to
`1`; no hypothesis on `q` or `u` is needed, in keeping with `HJO.Mellit.euclid`. -/
theorem omega_eq_slopeEval_mul {S : SweepSystem L q u} {Ω : ℕ → ℕ → ℕ → (S.W →ₗ[L] S.W)}
    (hΩ : IsReplicationFamily S Ω) {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {j : ℕ} (hj1 : 1 ≤ j) (hj3 : j ≤ 3) :
    Ω j a b = (-1 : L) ^ (a - 1) •
      (slopeEval (-S.y1) ((q * u)⁻¹ • S.z1) a b * Ω j 1 1) := by
  rw [euclid hΩ hab ha hb hj1 hj3, smul_smul, ← pow_add, ← two_mul, pow_mul]
  simp

end Omega

/-! ### The stage of `HJO.Mellit.stage` at the witness, written out

`HJO.Mellit.stage` is `(Z^{(k+1)}_{a,b})^{A-1}T_{k+1↘1}Ω(1;a,b)`, a map from the grading `k` to the
grading `k+1`. Each of its three factors acts degreewise, so the composite does, and its component
is the word below. -/

section Stage

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`Ω(1;a,b)` at the witness, on the grading `k`.** The operator
`(-1)^{a-1}Ξ_{a,b}(-y_1d^*_+)`, with `Ξ_{a,b}` the operator `HJO.Sweep.slopeOperator` at the
grading `k+1` and `d^*_+` the operator `HJO.Sweep.dplusStar` at the grading `k`. Raises the
grading by one. -/
noncomputable def replOneTotal (q u : L) (a b k : ℕ) : Module.End L (Total L) :=
  (-1 : L) ^ (a - 1) • (slopeOperator q u (k + 1) a b *
    -(LinearMap.mulLeft L (auxVar 1 : Total L) * dplusStar q u k))

/-- **`Ω(2;a,b)` at the witness, on the grading `k+1`.** The operator
`(-1)^{a-1}Ξ_{a,b}(-y_1z_1)`, with `z_1` the operator `HJO.Sweep.zop` at the grading `k+1`. -/
noncomputable def replTwoTotal (q u : L) (a b k : ℕ) : Module.End L (Total L) :=
  (-1 : L) ^ (a - 1) • (slopeOperator q u (k + 1) a b *
    -(LinearMap.mulLeft L (auxVar 1 : Total L) * zopOneStar q u (k + 1)))

/-- **`Z^{(k+1)}_{a,b}` of `HJO.Mellit.replicatedLetter` at the witness**,
`q^{-k}T_{k+1↘1}Ω(2;a,b)T_{1↗k+1}` on the grading `k+1`. -/
noncomputable def replicatedTotal (q u : L) (a b k : ℕ) : Module.End L (Total L) :=
  q ^ (-(k : ℤ)) • (trainDownEnd q (k + 1) 1 * replTwoTotal q u a b k * trainUpEnd q 1 (k + 1))

/-- **`G_{k+1,A}` of `HJO.Mellit.stage` at the witness**,
`(Z^{(k+1)}_{a,b})^{A-1}T_{k+1↘1}Ω(1;a,b)` as an endomorphism of `HJO.Sweep.Total L`: the
component on the grading `k` of `HJO.Mellit.stage`, by `HJO.Mellit.sweepWitness_stage_sweepIn`.
Every factor is an operator of the sweep and no replication family occurs. -/
noncomputable def stageTotal (q u : L) (a b k A : ℕ) : Module.End L (Total L) :=
  replicatedTotal q u a b k ^ (A - 1) * (trainDownEnd q (k + 1) 1 * replOneTotal q u a b k)

variable {q u : L} {a b : ℕ}

/-- **`Ω(1;a,b)` acts degreewise at the witness, by `HJO.Mellit.replOneTotal`.** -/
theorem sweepWitness_omega_one_sweepIn (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {Ω : ℕ → ℕ → ℕ → ((sweepWitness q u a b).W →ₗ[L] (sweepWitness q u a b).W)}
    (hΩ : IsReplicationFamily (sweepWitness q u a b) Ω) (k : ℕ) (F : Total L) :
    Ω 1 a b (sweepIn q u a b k F) = sweepIn q u a b (k + 1) (replOneTotal q u a b k F) := by
  have hbase : Ω 1 1 1 (sweepIn q u a b k F) = sweepIn q u a b (k + 1)
      ((-(LinearMap.mulLeft L (auxVar 1 : Total L) * dplusStar q u k)) F) := by
    rw [omega_one_one_one hΩ, LinearMap.neg_apply, LinearMap.comp_apply,
      sweepWitness_dplusStar_sweepIn, sweepWitness_y1_sweepIn, ← map_neg]
    rfl
  rw [omega_eq_slopeEval_mul hΩ hab ha hb (by omega) (by omega), LinearMap.smul_apply,
    Module.End.mul_apply, hbase, sweepWitness_slopeEval_sweepIn, ← map_smul, replOneTotal]
  rfl

/-- **`Ω(2;a,b)` acts degreewise at the witness, by `HJO.Mellit.replTwoTotal`.** -/
theorem sweepWitness_omega_two_sweepIn (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {Ω : ℕ → ℕ → ℕ → ((sweepWitness q u a b).W →ₗ[L] (sweepWitness q u a b).W)}
    (hΩ : IsReplicationFamily (sweepWitness q u a b) Ω) (k : ℕ) (F : Total L) :
    Ω 2 a b (sweepIn q u a b (k + 1) F)
      = sweepIn q u a b (k + 1) (replTwoTotal q u a b k F) := by
  have hbase : Ω 2 1 1 (sweepIn q u a b (k + 1) F) = sweepIn q u a b (k + 1)
      ((-(LinearMap.mulLeft L (auxVar 1 : Total L) * zopOneStar q u (k + 1))) F) := by
    rw [omega_two_one_one hΩ, LinearMap.neg_apply, LinearMap.comp_apply,
      sweepWitness_z1_sweepIn, sweepWitness_y1_sweepIn, ← map_neg]
    rfl
  rw [omega_eq_slopeEval_mul hΩ hab ha hb (by omega) (by omega), LinearMap.smul_apply,
    Module.End.mul_apply, hbase, sweepWitness_slopeEval_sweepIn, ← map_smul, replTwoTotal]
  rfl

/-- **`Z^{(k+1)}_{a,b}` acts degreewise at the witness, by `HJO.Mellit.replicatedTotal`.** -/
theorem sweepWitness_replicatedLetter_sweepIn (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {Ω : ℕ → ℕ → ℕ → ((sweepWitness q u a b).W →ₗ[L] (sweepWitness q u a b).W)}
    (hΩ : IsReplicationFamily (sweepWitness q u a b) Ω) (k : ℕ) (F : Total L) :
    replicatedLetter (sweepWitness q u a b) Ω a b k (sweepIn q u a b (k + 1) F)
      = sweepIn q u a b (k + 1) (replicatedTotal q u a b k F) := by
  rw [replicatedLetter, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    sweepWitness_trainUp_sweepIn, sweepWitness_omega_two_sweepIn hab ha hb hΩ,
    sweepWitness_trainDown_sweepIn, ← map_smul, replicatedTotal]
  rfl

/-- **The stage acts degreewise at the witness, by `HJO.Mellit.stageTotal`.** This is the
identification that removes the braid representation from the residual statement: the operator
standing to the left in the `append` field is, at this witness, the word
`(Z^{(k+1)}_{a,b})^{A-1}T_{k+1↘1}(-1)^{a-1}Ξ_{a,b}(-y_1d^*_+)` in the operators of the sweep. -/
theorem sweepWitness_stage_sweepIn (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {Ω : ℕ → ℕ → ℕ → ((sweepWitness q u a b).W →ₗ[L] (sweepWitness q u a b).W)}
    (hΩ : IsReplicationFamily (sweepWitness q u a b) Ω) (k A : ℕ) (F : Total L) :
    stage (sweepWitness q u a b) Ω a b k A (sweepIn q u a b k F)
      = sweepIn q u a b (k + 1) (stageTotal q u a b k A F) := by
  rw [stage, LinearMap.comp_apply, LinearMap.comp_apply,
    sweepWitness_omega_one_sweepIn hab ha hb hΩ, sweepWitness_trainDown_sweepIn,
    pow_apply_comm _ (sweepWitness_replicatedLetter_sweepIn hab ha hb hΩ k), stageTotal]
  rfl

end Stage

/-! ### The residual identity -/

section Residue

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {a b : ℕ}

/-- **The forced braid value, written out.** `HJO.Mellit.braidValue` is `D_{η,c_α}` at
`η = a·α.sum + 1/2`, and at the witness that is `HJO.Mellit.dsc` in the grading `α.length`: the
two conventions the `D` field's arity forces are identities on the colourings of a composition,
`HJO.Mellit.colourParts_compColouring` and `HJO.Mellit.colourMult_compColouring`. -/
theorem braidValue_eq_sweepIn (ha : 0 < a) (hb : 0 < b) {α : List ℕ} (hpos : ∀ x ∈ α, 0 < x) :
    braidValue q u a b α = sweepIn q u a b α.length
      (dsc q u a b α.sum (sepLevel a α.sum) (compColouring a b α)) := by
  change gradedIn L (colourParts (compColouring a b α))
      (dsc q u a b (colourMult b (compColouring a b α)) (sepLevel a α.sum)
        (compColouring a b α)) = gradedIn L α.length _
  rw [colourParts_compColouring ha hb hpos, colourMult_compColouring hb]

/-- Appending a positive part to a composition with positive parts. -/
theorem forall_pos_append_singleton {α : List ℕ} {A : ℕ} (hpos : ∀ x ∈ α, 0 < x) (hA : 0 < A) :
    ∀ x ∈ α ++ [A], 0 < x := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact hpos x h
  · rw [List.mem_singleton] at h
    omega

/-- **What the `append` field of `HJO.Mellit.IsBraidValue` says at the sweep witness.** An
identity in `HJO.Sweep.Total L` between the invariant of `HJO.Mellit.dsc` at `c_{α ++ (A)}` and
the stage `G_{ℓ+1,A}` of `HJO.Mellit.stage` applied to the invariant at `c_α`, with the scalar
`(-1)^{(a-1)A}(qu)^{1-A}` of `HJO.Mellit.braidRep_specialBraid_dplusIter`. Each invariant is read at
the separating admissible level `HJO.Mellit.sepLevel` of its own rectangle; by
`HJO.Mellit.dsc_compColouring_congr_level` no other separating admissible level would give a
different statement.

The hypotheses are the field's own: the parts of `α` are positive and `0 < A`. Nothing about the
braid representation occurs, and by
`HJO.Mellit.mellitInduction_sweepWitness_iff_sweepAppend` this single identity is *equivalent* to
`HJO.Mellit.MellitInduction` at the witness.

**The hypothesis-free reading of this identity is false at `q = 1` and `a = 1` — both of which lie
outside the quantification any consumer uses.** So what follows is a statement about which
*parameters* are degenerate, and **not** a defect in the shuffle assembly: it is not a reason to
repair or replace the witness. The very same instance is a *theorem* at every `q ≠ 1`
(`HJO.Mellit.sweepAppend_nil_one_one_two`, `HJO/Shuffle/SweepAppendOneTwo.lean`), so `q ≠ 1` is
the whole of what the bare `Prop` is missing there.

The refutation is `HJO.Mellit.not_sweepAppend_one_left`
(`HJO/Shuffle/SweepAppendRefuted.lean`), at `q = 1`, `a = 1`, every `1 < b`, where
`HJO.Sweep.corner` degenerates to the zero map and the left-hand side vanishes on every path. There
is no condition on `q` or `u` in this definition to exclude that, and adding one would break the
hypothesis-free `iff` above — which is the only thing the degeneracy forbids.

This does not make `HJO.Mellit.MellitInduction` false in the range that matters, and the shuffle
side does not need the witness repaired. "As stated" means the bare `Prop` at a fixed
`(q, u, a, b)`, and **that is not what any consumer asks for.** The binder is `hind` of
`HJO.Mellit.shuffle_of_lhs_and_induction` (`HJO/Shuffle/SweepComputesClosed.lean`):

`∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b →
  MellitInduction (sweepWitness q u a b) a b`

and **every known refutation lies outside that quantification**, the headline one on two independent
counts:

* `not_sweepAppend_one_left` needs `q = 1` **and** `a = 1`. The `AlgebraicIndependent` hypothesis
  gives `q ≠ 1` (`HJO.Mellit.ne_one_of_algebraicIndependent_fst`,
  `HJO/Shuffle/SweepAppendGeneric.lean`; and `sub_one_ne_zero_of_algebraicIndependent_fst`,
  `SweepComputesClosed.lean`), and the binder separately demands `1 < a`.
* the `q = 0` and `u = 0` refutations (`HJO.Mellit.append_scalar_eq_zero`,
  `HJO/Shuffle/SweepAppendNilDegenerate.lean`, and the `(2,3)` instances) are excluded by
  the same algebraic independence.
* the `hzero` refutations at `(a,b) = (1,2)` need `a = 1`, again out of range.

So the falsity of the bare `Prop` is a statement about which *parameters* are degenerate, not an
obstruction to the goal. What it does forbid is adding genericity to the hypothesis-free `iff`s in
this file — a per-`q` equivalence cannot carry it — and that is the only thing it forbids.

This is **not** `HJO.Mellit.braidRep_specialBraid_dplusIter`, which states the same shape of
identity about `π_{k+1}(B_{s,w,β})d_+^{k+1}(1)` in the vocabulary of `HJO.Sweep.braidRep` and
`HJO.Braid.specialBraid`; neither this definition nor anything below is a form of that statement. -/
def SweepAppend (q u : L) (a b : ℕ) : Prop :=
  ∀ (α : List ℕ) (A : ℕ), (∀ x ∈ α, 0 < x) → 0 < A →
    dsc q u a b (α.sum + A) (sepLevel a (α.sum + A)) (compColouring a b (α ++ [A]))
      = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
          stageTotal q u a b α.length A
            (dsc q u a b α.sum (sepLevel a α.sum) (compColouring a b α))

/-- **The `append` field at the witness is `HJO.Mellit.SweepAppend`, one composition at a time.**
Both sides live in the grading `α.length + 1`, and `HJO.Mellit.sweepIn_injective` is what makes this
an equivalence rather than a one-way reading. -/
theorem braidValue_append_iff (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {Ω : ℕ → ℕ → ℕ → ((sweepWitness q u a b).W →ₗ[L] (sweepWitness q u a b).W)}
    (hΩ : IsReplicationFamily (sweepWitness q u a b) Ω) {α : List ℕ} {A : ℕ}
    (hpos : ∀ x ∈ α, 0 < x) (hA : 0 < A) :
    braidValue q u a b (α ++ [A]) = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
        stage (sweepWitness q u a b) Ω a b α.length A (braidValue q u a b α)
      ↔ dsc q u a b (α.sum + A) (sepLevel a (α.sum + A)) (compColouring a b (α ++ [A]))
          = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
              stageTotal q u a b α.length A
                (dsc q u a b α.sum (sepLevel a α.sum) (compColouring a b α)) := by
  have hsum : (α ++ [A]).sum = α.sum + A := by
    simp only [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
  have hlen : (α ++ [A]).length = α.length + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
  rw [braidValue_eq_sweepIn ha hb (forall_pos_append_singleton hpos hA),
    braidValue_eq_sweepIn ha hb hpos, hsum, hlen, sweepWitness_stage_sweepIn hab ha hb hΩ,
    ← map_smul]
  exact (sweepIn_injective q u a b (α.length + 1)).eq_iff

/-- **`HJO.Mellit.IsBraidValue` holds of the forced braid value exactly when
`HJO.Mellit.SweepAppend` does.** The `nil` field is `HJO.Mellit.braidValue_nil`, already proved, so
the whole structure is the `append` field, and that is the residual identity composition by
composition. -/
theorem isBraidValue_sweepWitness_iff (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {Ω : ℕ → ℕ → ℕ → ((sweepWitness q u a b).W →ₗ[L] (sweepWitness q u a b).W)}
    (hΩ : IsReplicationFamily (sweepWitness q u a b) Ω) :
    IsBraidValue (sweepWitness q u a b) Ω a b (braidValue q u a b) ↔ SweepAppend q u a b := by
  constructor
  · intro hB α A hpos hA
    exact (braidValue_append_iff hab ha hb hΩ hpos hA).1 (hB.append α A hpos hA)
  · intro h
    refine ⟨braidValue_nil q u hab ha hb, fun α A hpos hA => ?_⟩
    exact (braidValue_append_iff hab ha hb hΩ hpos hA).2 (h α A hpos hA)

/-- **`HJO.Mellit.BraidClosedForm` at the witness is exactly `HJO.Mellit.SweepAppend`.**

Read left to right: a braid value for the witness gives the residual identity. The braid value is
not assumed to be `HJO.Mellit.braidValue` — it is *forced* to be, because
`HJO.Mellit.IsColouringValue` pins `B α` at every composition with positive parts, read at
`HJO.Mellit.sepLevel`, which is admissible and separating by
`HJO.Mellit.separatesDiagonal_sepLevel'`.

Read right to left: the identity gives the whole conjunction, the replication family by
`HJO.Mellit.replExists` and `HJO.Mellit.IsColouringValue` by
`HJO.Mellit.isColouringValue_sweepWitness`. -/
theorem braidClosedForm_sweepWitness_iff_sweepAppend (hab : Nat.Coprime a b) (ha : 0 < a)
    (hb : 0 < b) : BraidClosedForm (sweepWitness q u a b) a b ↔ SweepAppend q u a b := by
  constructor
  · rintro ⟨Ω, B, hΩ, hB, hD⟩
    have hval : ∀ α : List ℕ, (∀ x ∈ α, 0 < x) → B α = braidValue q u a b α := fun α hpos =>
      (hD α.sum (sepLevel a α.sum) (isAdmissibleLevel_sepLevel a α.sum)
        (separatesDiagonal_sepLevel' a b α.sum) α hpos rfl).symm
    refine (isBraidValue_sweepWitness_iff hab ha hb hΩ).1 ⟨?_, fun α A hpos hA => ?_⟩
    · rw [← hval [] (List.forall_mem_nil _)]
      exact hB.nil
    · rw [← hval _ (forall_pos_append_singleton hpos hA), ← hval α hpos]
      exact hB.append α A hpos hA
  · intro h
    obtain ⟨Ω, hΩ⟩ := replExists (sweepWitness q u a b)
    exact ⟨Ω, braidValue q u a b, hΩ, (isBraidValue_sweepWitness_iff hab ha hb hΩ).2 h,
      isColouringValue_sweepWitness q u hab ha hb⟩

/-- **`HJO.Mellit.mellitInduction_sweepWitness` at the sweep witness is one identity about
`HJO.Mellit.dsc`.** Composing `HJO.Mellit.mellitInduction_iff_braidClosedForm` with
`HJO.Mellit.braidClosedForm_sweepWitness_iff_sweepAppend`: the clause of
`HJO.Mellit.MellitInput` that the shuffle side needs at this witness is equivalent to
`HJO.Mellit.SweepAppend`, an identity between two sums of partial sweep words with
`HJO.Mellit.stage` in between.

`0 < a`, `0 < b` and coprimality are all that is spent — the `1 < a < b` is not needed
here — and there is no hypothesis on `q` or `u`, in keeping with
`HJO.Mellit.mellitInduction_iff_braidClosedForm` and `HJO.Mellit.euclid`.

**Genericity is not spent inside `HJO.Mellit.SweepAppend`.** There is no genericity inside
`SweepAppend` to spend: it carries no hypothesis on `q`
either, and `HJO.Mellit.not_sweepAppend_one_left` refutes both sides of this `iff` at `q = 1`. An
`iff` between two false statements is proved as easily as one between two true ones, and both halves
of this one were proved. The genericity has to come from the consumer's quantifier —
`HJO.Mellit.shuffle_of_lhs_and_induction`'s `AlgebraicIndependent ℤ ![q, u]`, which gives `q ≠ 1`
by `HJO.Mellit.sub_one_ne_zero_of_algebraicIndependent_fst` — so this equivalence is usable only
under a hypothesis it does not state, and a proof of either side must restate it at a generic `q`.
What *is* true of the third Stern–Brocot rule of `HJO.Mellit.IsReplicationFamily` is that it has
already been paid out into the `(qu)^{-1}` scalars of `HJO.Mellit.replTwoTotal`. -/
theorem mellitInduction_sweepWitness_iff_sweepAppend (hab : Nat.Coprime a b) (ha : 0 < a)
    (hb : 0 < b) : MellitInduction (sweepWitness q u a b) a b ↔ SweepAppend q u a b :=
  (mellitInduction_iff_braidClosedForm hab ha).trans
    (braidClosedForm_sweepWitness_iff_sweepAppend hab ha hb)

/-! ### The identity between the two path sums

`HJO.Mellit.dsc_compColouring_eq_sum_partialSweepWord` replaces each invariant by a sum of partial
sweep words over `HJO.Mellit.aboveReturnPaths` — an index set with no level in it — and
`HJO.Mellit.sweptAbove_eq_filter` makes each summand level-free too. This is the form the identity
has to be attacked in. -/

/-- **`HJO.Mellit.SweepAppend` as a relation between two sums of partial sweep words.** The left
sum runs over the above-diagonal `(a(N+A), b(N+A))`-paths of return composition `α ++ (A)` and the
right over the above-diagonal `(aN, bN)`-paths of return composition `α`, and the stage is applied
inside the sum by linearity. No level appears in either index set. -/
theorem sweepAppend_iff_sum (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) :
    SweepAppend q u a b ↔ ∀ (α : List ℕ) (A : ℕ), (∀ x ∈ α, 0 < x) → 0 < A →
      ∑ y ∈ aboveReturnPaths a b (α.sum + A) (α ++ [A]),
          partialSweepWord q u y (sepLevel a (α.sum + A)) (1 : Total L)
        = ∑ y ∈ aboveReturnPaths a b α.sum α,
            ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
              stageTotal q u a b α.length A (partialSweepWord q u y (sepLevel a α.sum)
                (1 : Total L)) := by
  have key : ∀ (α : List ℕ) (A : ℕ), (∀ x ∈ α, 0 < x) → 0 < A →
      (dsc q u a b (α.sum + A) (sepLevel a (α.sum + A)) (compColouring a b (α ++ [A]))
          = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
              stageTotal q u a b α.length A
                (dsc q u a b α.sum (sepLevel a α.sum) (compColouring a b α))
        ↔ ∑ y ∈ aboveReturnPaths a b (α.sum + A) (α ++ [A]),
              partialSweepWord q u y (sepLevel a (α.sum + A)) (1 : Total L)
            = ∑ y ∈ aboveReturnPaths a b α.sum α,
                ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
                  stageTotal q u a b α.length A (partialSweepWord q u y (sepLevel a α.sum)
                    (1 : Total L))) := by
    intro α A hpos hA
    have hsum : (α ++ [A]).sum = α.sum + A := by
      simp only [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [dsc_compColouring_eq_sum_partialSweepWord q u (isAdmissibleLevel_sepLevel a (α.sum + A))
        (separatesDiagonal_sepLevel' a b (α.sum + A)) hab ha hb
        (forall_pos_append_singleton hpos hA) hsum,
      dsc_compColouring_eq_sum_partialSweepWord q u (isAdmissibleLevel_sepLevel a α.sum)
        (separatesDiagonal_sepLevel' a b α.sum) hab ha hb hpos rfl,
      map_sum, Finset.smul_sum]
  exact ⟨fun h α A hpos hA => (key α A hpos hA).1 (h α A hpos hA),
    fun h α A hpos hA => (key α A hpos hA).2 (h α A hpos hA)⟩

/-! ### The two corners the field can be read in closed form at

`α = []` with `0 < A` is the first step off the `nil` field, and `A = 1` is where the power of the
replicated letter is empty. Both are inside `HJO.Mellit.SweepAppend`'s range of quantification, and
in both the stage collapses: at `k = 0` the two trains are empty words, and at `A = 1` the sign of
the field cancels the sign `HJO.Mellit.euclid` puts into `HJO.Mellit.replOneTotal`. -/

omit [Algebra ℚ L] in
/-- `T_{1↘1} = 1`: the descending train of `HJO.Braid.trainDown` at a rank it cannot move in. -/
theorem trainDownEnd_one_one (q : L) : trainDownEnd q 1 1 = 1 :=
  Braid.trainDown_self _ _ 1

omit [Algebra ℚ L] in
/-- `T_{1↗1} = 1`: the ascending train of `HJO.Braid.trainUp` at a rank it cannot move in. -/
theorem trainUpEnd_one_one (q : L) : trainUpEnd q 1 1 = 1 :=
  Braid.trainUp_self _ _ 1

/-- **At the grading `0` the replicated letter is `Ω(2;a,b)` itself**: both conjugating trains are
empty and the scalar `q^{-k}` of `HJO.Mellit.replicatedLetter` is `q^0`. -/
theorem replicatedTotal_zero : replicatedTotal q u a b 0 = replTwoTotal q u a b 0 := by
  rw [replicatedTotal, trainDownEnd_one_one, trainUpEnd_one_one]
  simp

/-- **The stage at the grading `0`, in closed form.** `G_{1,A} = Ω(2;a,b)^{A-1}Ω(1;a,b)`: the
operator the `α = []` instance of `HJO.Mellit.SweepAppend` applies to the vacuum. -/
theorem stageTotal_zero (A : ℕ) : stageTotal q u a b 0 A
    = replTwoTotal q u a b 0 ^ (A - 1) * replOneTotal q u a b 0 := by
  rw [stageTotal, replicatedTotal_zero, trainDownEnd_one_one, one_mul]

/-- **The stage at `A = 1`, in closed form.** `G_{k+1,1} = T_{k+1↘1}Ω(1;a,b)`, the power of the
replicated letter being empty. -/
theorem stageTotal_one (k : ℕ) :
    stageTotal q u a b k 1 = trainDownEnd q (k + 1) 1 * replOneTotal q u a b k := by
  rw [stageTotal, Nat.sub_self, pow_zero, one_mul]

omit [Algebra ℚ L] in
/-- A power of `-y_1` acts by multiplication by `(-y_1)^m`: the slope operator at `(1,n)` is such a
power, by `HJO.Mellit.slopeEval_one_left`. -/
theorem neg_mulLeft_pow_apply (x : Total L) (m : ℕ) (F : Total L) :
    ((-LinearMap.mulLeft L x) ^ m) F = (-x) ^ m * F := by
  induction m generalizing F with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, LinearMap.neg_apply, LinearMap.mulLeft_apply, pow_succ]
    ring

/-- **`Ω(1;1,b)` sends the vacuum to `(-y_1)^b`.** At `a = 1` the slope word of
`HJO.Braid.slopeBraid` has no `𝗓`, so `Ξ_{1,b} = (-y_1)^{b-1}` by
`HJO.Mellit.slopeEval_one_left`, and `d^*_+(1) = 1`. -/
theorem replOneTotal_one_left (q u : L) {b : ℕ} (hb : 0 < b) :
    replOneTotal q u 1 b 0 (1 : Total L) = (-(auxVar 1 : Total L)) ^ b := by
  have hd : dplusStar q u 0 (1 : Total L) = 1 := by
    rw [dplusStar_apply, map_one, map_one]
  rw [replOneTotal, LinearMap.smul_apply, Nat.sub_self, pow_zero, one_smul,
    Module.End.mul_apply, LinearMap.neg_apply, Module.End.mul_apply, hd,
    LinearMap.mulLeft_apply, mul_one, slopeOperator_eq_slopeEval,
    slopeEval_one_left _ _ hb, neg_mulLeft_pow_apply, ← pow_succ,
    show b - 1 + 1 = b from by omega]

/-- **Value check: `G_{1,1}(1) = (-y_1)^b` at `(a,b) = (1,b)`.** -/
theorem stageTotal_one_left (q u : L) {b : ℕ} (hb : 0 < b) :
    stageTotal q u 1 b 0 1 (1 : Total L) = (-(auxVar 1 : Total L)) ^ b := by
  rw [stageTotal_one, Module.End.mul_apply, replOneTotal_one_left q u hb, trainDownEnd_one_one]
  rfl

/-- **The stage is not the zero map, and `HJO.Mellit.SweepAppend` is therefore not vacuous.** The
guard the three `shape_*` fields of `HJO.Mellit.SweepSystem` cannot provide — the zero operator
satisfies all three, and a stage that had collapsed to zero would make the residual identity say
`D_{η,c_{α ++ (A)}} = 0`. At `(a,b) = (1,b)`, `α = []` and `A = 1` the stage sends the vacuum to
`(-y_1)^b`, which is a nonzero element of `HJO.Sweep.Total L` because `y_1` is one of the
polynomial ring's own variables. So at those parameters the identity asserts
`D_{η,c_{(1)}} = (-y_1)^b` of the `1 × b` rectangle, which is a claim with content. -/
theorem stageTotal_one_left_ne_zero (q u : L) {b : ℕ} (hb : 0 < b) :
    stageTotal q u 1 b 0 1 (1 : Total L) ≠ 0 := by
  rw [stageTotal_one_left q u hb]
  exact pow_ne_zero b (neg_ne_zero.2 (by rw [auxVar]; exact MvPolynomial.X_ne_zero _))

/-- **The `α = []` instance of `HJO.Mellit.SweepAppend`, in closed form.** The right-hand side reads
`D_{1/2,∅} = 1` by `HJO.Mellit.dsc_empty_eq_one`, and the stage collapses by
`HJO.Mellit.stageTotal_zero`, so the first step off the `nil` field asserts
`D_{η,c_{(A)}} = (-1)^{(a-1)A}(qu)^{1-A}Ω(2;a,b)^{A-1}Ω(1;a,b)(1)` — an identity with no
composition and no train in it. This is the base case any proof of
`HJO.Mellit.SweepAppend` has to start from. -/
theorem dsc_singleton_of_sweepAppend (h : SweepAppend q u a b) (hab : Nat.Coprime a b) (ha : 0 < a)
    (hb : 0 < b) {A : ℕ} (hA : 0 < A) :
    dsc q u a b A (sepLevel a A) (compColouring a b [A])
      = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
          (replTwoTotal q u a b 0 ^ (A - 1)) (replOneTotal q u a b 0 (1 : Total L)) := by
  have hc : compColouring a b ([] : List ℕ) = (∅ : Finset (ℕ × ℕ)) := by simp [compColouring]
  have hone : dsc q u a b 0 (sepLevel a 0) (compColouring a b ([] : List ℕ)) = (1 : Total L) := by
    rw [hc]
    exact dsc_empty_eq_one q u (isAdmissibleLevel_sepLevel a 0)
      (separatesDiagonal_sepLevel' a b 0) hab ha hb
  have h0 := h [] A (List.forall_mem_nil _) hA
  simp only [List.sum_nil, List.length_nil, List.nil_append, Nat.zero_add] at h0
  rw [hone, stageTotal_zero, Module.End.mul_apply] at h0
  exact h0

/-- **The `A = 1` instance of `HJO.Mellit.SweepAppend`, in closed form.** The field's scalar is
`(-1)^{a-1}` there, and `HJO.Mellit.euclid` has put a second `(-1)^{a-1}` into
`HJO.Mellit.replOneTotal`, so the two cancel and `A = 1` is sign-free:
`D_{η,c_{α ++ (1)}} = T_{ℓ+1↘1}Ξ_{a,b}(-y_1d^*_+ D_{η,c_α})`. So the corner where the power of the
replicated letter is empty carries no scalar at all. -/
theorem dsc_append_one_of_sweepAppend (h : SweepAppend q u a b) {α : List ℕ}
    (hpos : ∀ x ∈ α, 0 < x) :
    dsc q u a b (α.sum + 1) (sepLevel a (α.sum + 1)) (compColouring a b (α ++ [1]))
      = trainDownEnd q (α.length + 1) 1 (slopeOperator q u (α.length + 1) a b
          (-(LinearMap.mulLeft L (auxVar 1 : Total L)
            (dplusStar q u α.length (dsc q u a b α.sum (sepLevel a α.sum)
              (compColouring a b α)))))) := by
  have hop : ∀ X : Total L, ((-1 : L) ^ ((a - 1) * 1) * (q * u) ^ (1 - ((1 : ℕ) : ℤ))) •
      trainDownEnd q (α.length + 1) 1 (replOneTotal q u a b α.length X)
        = trainDownEnd q (α.length + 1) 1 (slopeOperator q u (α.length + 1) a b
            (-(LinearMap.mulLeft L (auxVar 1 : Total L) (dplusStar q u α.length X)))) := by
    intro X
    rw [replOneTotal, LinearMap.smul_apply, map_smul, smul_smul, Nat.mul_one, Nat.cast_one,
      sub_self, zpow_zero, mul_one, ← pow_add, ← two_mul, pow_mul]
    simp [Module.End.mul_apply]
  have h1 := h α 1 hpos Nat.one_pos
  rw [stageTotal_one, Module.End.mul_apply] at h1
  rw [h1, hop]

/-! ### One thing the comparison of the two sums needs, and does not have to worry about

The two sums of `HJO.Mellit.sweepAppend_iff_sum` live in different rectangles — the left in
`a(N+A) × b(N+A)` and the right in `aN × bN` — and `HJO.ParkingFunctions.abovePointRank` carries
the rectangle: the rank of one and the same lattice point is `(a(N+A)+1)(N+A)(ay-bx) + x` on the
left and `(aN+1)N(ay-bx) + x` on the right. Since `HJO.Mellit.partialSweepWord` multiplies its
factors along `HJO.Mellit.sortByRank`, whose key is that rank, the first question about the
comparison is whether the two listings of a shared set of points even agree. They do: the
rectangle enters only as a positive multiplier, and on the strip `0 ≤ x ≤ aN` the abscissa
tie-break is smaller than it. -/

section RankOrder

variable {a b N : ℕ}

/-- **The rank order on the strip is lexicographic in `(ay - bx, x)`, with no rectangle in it.**
`HJO.ParkingFunctions.abovePointRank a b N x y` is `M(ay - bx) + x` with `M = (aN+1)N`, and
`x, x' ≤ aN < M`, so the multiplier decides the comparison unless the diagonal excesses agree, in
which case the abscissas do. `0 < N` is needed and is not decoration: at `N = 0` the multiplier is
`0` and the rank ignores the ordinate — the same corner that makes
`HJO.Paths.abovePointRank_injOn` carry it. -/
theorem abovePointRank_le_iff (hN : 0 < N) {x y x' y' : ℕ} (hx : x ≤ a * N) (hx' : x' ≤ a * N) :
    ParkingFunctions.abovePointRank a b N x y ≤ ParkingFunctions.abovePointRank a b N x' y' ↔
      ((a : ℤ) * y - b * x < (a : ℤ) * y' - b * x' ∨
        ((a : ℤ) * y - b * x = (a : ℤ) * y' - b * x' ∧ x ≤ x')) := by
  have h1 : (x : ℤ) ≤ (a : ℤ) * N := by exact_mod_cast hx
  have h2 : (x' : ℤ) ≤ (a : ℤ) * N := by exact_mod_cast hx'
  have h3 : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  have h4 : (0 : ℤ) ≤ (a : ℤ) * N := by positivity
  have h5 : (0 : ℤ) ≤ (x : ℤ) := Int.natCast_nonneg _
  have h6 : (0 : ℤ) ≤ (x' : ℤ) := Int.natCast_nonneg _
  have hc : (a : ℤ) * N + 1 ≤ ((a : ℤ) * N + 1) * N := by nlinarith
  simp only [ParkingFunctions.abovePointRank]
  constructor
  · intro h
    rcases lt_trichotomy ((a : ℤ) * y - b * x) ((a : ℤ) * y' - b * x') with hlt | heq | hgt
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, by exact_mod_cast (by nlinarith : (x : ℤ) ≤ x')⟩
    · exact absurd h (by nlinarith)
  · rintro (hlt | ⟨heq, hle⟩)
    · nlinarith
    · have hxx : (x : ℤ) ≤ x' := by exact_mod_cast hle
      nlinarith

/-- **Two rectangles rank a shared pair of points in the same order.** So the rank-order listing
`HJO.Mellit.sortByRank` of a set of lattice points lying in both strips — which is what the
comparison of the two sums of `HJO.Mellit.sweepAppend_iff_sum` has to perform — does not depend on
which of the two rectangles it is computed in. The `N`-dependence of the rank is therefore *not* an
obstruction to that comparison; what is left of it is that the extension has north steps the
truncation does not, which is what the trains and the replicated letter of
`HJO.Mellit.replicatedLetter` are there to account for. -/
theorem abovePointRank_le_congr {M : ℕ} (hN : 0 < N) (hM : 0 < M) {x y x' y' : ℕ}
    (hx : x ≤ a * N) (hx' : x' ≤ a * N) (hxM : x ≤ a * M) (hx'M : x' ≤ a * M) :
    (ParkingFunctions.abovePointRank a b N x y ≤ ParkingFunctions.abovePointRank a b N x' y')
      ↔ (ParkingFunctions.abovePointRank a b M x y
          ≤ ParkingFunctions.abovePointRank a b M x' y') := by
  rw [abovePointRank_le_iff hN hx hx', abovePointRank_le_iff hM hxM hx'M]

end RankOrder

end Residue

end HJO.Mellit
