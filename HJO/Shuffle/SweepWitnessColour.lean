/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitRem41
public import HJO.Shuffle.MellitStageInduction
public import HJO.Shuffle.SweepWitness
public meta import HJO.Attr

/-! # The two data the `D` field's arity drops, read back off a colouring

`HJO.Mellit.SweepSystem.D` has arity `ℚ → Finset (ℕ × ℕ) → W` while the `D_{η,c}` of
`HJO.Mellit.dsc` — takes `a b N η c`, and the grading it must live in is the
number of parts `ℓ`. The pair `(a, b)` is fixed before the sweep system inside
`HJO.Mellit.MellitInput`, so `HJO.Mellit.sweepWitness` carries it as a parameter; `N` and `ℓ` are
quantified *after* the system, inside `HJO.Mellit.MellitInduction` and `HJO.Mellit.Rem41`, so the
witness reads them back off the colouring by `HJO.Mellit.colourMult` and
`HJO.Mellit.colourParts`. This file proves that both functions return the intended values on the
colourings the interface reads.

## The two identities

On the colourings the interface applies `D` to — the `c_α` of `HJO.Mellit.compColouring`, and
`∅ = c_[]`, which is the only colouring `HJO.Mellit.MellitInduction` reads at `N = 0` —

* `HJO.Mellit.colourMult_compColouring`: `colourMult b c_α = α.sum`, for every `α` and every
  `b ≥ 1`. The largest ordinate of `c_α` is `bN`, attained at the foot of the east step arriving at
  the final touch point, so the division is exact.
* `HJO.Mellit.colourParts_compColouring`: `colourParts c_α = α.length`, for `a, b ≥ 1` and every
  part of `α` positive. Each of the two families of `HJO.Mellit.compColouring` has `ℓ` elements and
  they are disjoint, so `#c_α = 2ℓ` and again the division is exact.

`HJO.Mellit.sweepWitness_proj_dminus_pow_D` is what the two buy: the identity
`proj (d_-^ℓ D_{η,c_α}) = constantCoeff (lowerRun q ℓ (dsc q u a b N η c_α))`, which is the
hypothesis `hD` of `HJO.Mellit.rem41_of_sweepComputes`, holds *of the witness*.

## Where each identity stops, machine-checked

Both formulas divide in `ℕ`, so each has a locus where it is false rather than merely unproved, and
the three corners are recorded as `decide`-checked refutations:

* `HJO.Mellit.colourParts_compColouring_zero_part` — at `α = [0]` the two families coincide, `c_α`
  is the single cell `(0,0)`, and `colourParts` reads `0` where `α.length` is `1`. So the parts
  identity genuinely needs every part positive, and the hypothesis `hD` of
  `HJO.Mellit.rem41_of_sweepComputes`, which quantifies over every `α` of sum `N` with no positivity
  condition, is **not** satisfied by the witness as it stands: it has to be scoped to the
  compositions its own conclusion is about. Narrowing it costs nothing — the proof of that theorem
  has `hpos` in hand at the one place it uses `hD`.
* `HJO.Mellit.colourParts_compColouring_a_zero` — at `a = 0` the western neighbour `aA_i - 1` *is*
  `aA_i`, the two families overlap in `ℓ - 1` cells, and `colourParts` reads `1` where `α.length`
  is `2`.
* `HJO.Mellit.colourMult_compColouring_b_zero` — at `b = 0` every ordinate is `0` and the truncating
  division reads `N = 0`.

All three are excluded by the standing hypotheses `1 < a < b` and by the positivity of
the parts of a composition, and `HJO.Mellit.rem41_of_sweepComputes` already carries `0 < a` and
`0 < b`; only the positivity of the parts is missing from `hD`.

## The path colouring is *not* a locus where the multiplier identity holds

`HJO.Mellit.colourMult_colouring_ne` refutes the same formula read on `HJO.Mellit.colouring y η`,
the colouring of `HJO.Mellit.colouring`: the `(2,3)`-path of height vector `(0,2,3)` at the level
`21/2` is coloured `{(0,1), (0,2)}`, whose largest ordinate is `2`, and `2 / 3 = 0 ≠ 1 = N`. The
colouring of a path records only the cells the level line crosses, and nothing makes the top of the
rectangle one of them; it is `c_α`, whose second family is indexed by *all* the touch points, that
determines `N`.

This leaves no gap: `HJO.Mellit.SweepSystem.D` is read at `c_α` only — in
`HJO.Mellit.MellitInduction`, `HJO.Mellit.Rem41` and `HJO.Mellit.MellitInduction`'s consequence at
the empty colouring — and `HJO.Mellit.colouring y η` equals `c_α` exactly when the path has return
composition `α`, by `HJO.Mellit.colouring_eq_compColouring_iff`, at which point the identity that
applies is the one proved here. But it does say that the witness's `D` must never be applied to a
general admissible colouring, and that a clause that did so would be reading a junk value.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open HJO.Sweep Paths

/-! ### The multiplier -/

/-- **The largest ordinate of `c_α` is `bN`.** Every cell of either family of
`HJO.Mellit.compColouring` has ordinate `b` times a partial sum of `α`, and the last cell of the
second family has ordinate `b` times the whole sum. At `α = []` the colouring is empty and both
sides are `0`. -/
theorem sup_snd_compColouring (a b : ℕ) (α : List ℕ) :
    (compColouring a b α).sup (fun p => p.2) = b * α.sum := by
  rcases eq_or_ne α [] with rfl | h
  · simp [compColouring]
  · refine le_antisymm (Finset.sup_le fun p hp => snd_le_of_mem_compColouring hp) ?_
    exact Finset.le_sup (f := fun p : ℕ × ℕ => p.2) (mem_compColouring_top h)

/-- **The multiplier convention of `HJO.Mellit.sweepWitness` is an identity.**
`colourMult b c_α = N`: the truncating division of `HJO.Mellit.colourMult` is exact on the
colourings the interface applies `D` to, the largest ordinate of `c_α` being `bN`. No condition on
`α` — the empty composition included, where both sides are `0` — and `0 < b` is the only
hypothesis, which follows from the standing `1 < a < b` and is a hypothesis of
`HJO.Mellit.rem41_of_sweepComputes`. It is needed:
`HJO.Mellit.colourMult_compColouring_b_zero`. -/
theorem colourMult_compColouring {b : ℕ} (hb : 0 < b) (a : ℕ) (α : List ℕ) :
    colourMult b (compColouring a b α) = α.sum := by
  rw [colourMult, sup_snd_compColouring, Nat.mul_div_cancel_left _ hb]

/-! ### The number of parts -/

/-- **`c_α` has `2ℓ` cells.** The two families of `HJO.Mellit.compColouring` have `ℓ` cells each
and are disjoint. Each is `ℓ` because a cell determines its ordinate, the ordinate determines the
partial sum (`0 < b`), and the partial sums of a composition with positive parts increase strictly.
They are disjoint because a shared cell would have `aA_i = aA_j - 1` with `A_i = A_j` and
`A_j > 0` — the second family is indexed by the *nonzero* partial sums — and `aA_j ≥ 1` makes
`aA_j - 1 < aA_j`. -/
theorem card_compColouring {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {α : List ℕ}
    (hpos : ∀ x ∈ α, 0 < x) : (compColouring a b α).card = 2 * α.length := by
  have hinj : ∀ i j, i ≤ α.length → j ≤ α.length → (α.take i).sum = (α.take j).sum → i = j := by
    intro i j hi hj hij
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hij (by have := sum_take_lt hpos h hj; omega)
    · exact h
    · exact absurd hij (by have := sum_take_lt hpos h hi; omega)
  have h1 : ((range α.length).image fun i => (a * (α.take i).sum, b * (α.take i).sum)).card
      = α.length := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact hinj i j hi.le hj.le (Nat.eq_of_mul_eq_mul_left hb (congrArg Prod.snd hij))
  have h2 : ((range α.length).image
      fun i => (a * (α.take (i + 1)).sum - 1, b * (α.take (i + 1)).sum)).card = α.length := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have := hinj (i + 1) (j + 1) (by omega) (by omega)
      (Nat.eq_of_mul_eq_mul_left hb (congrArg Prod.snd hij))
    omega
  have hdisj : Disjoint ((range α.length).image fun i => (a * (α.take i).sum, b * (α.take i).sum))
      ((range α.length).image
        fun i => (a * (α.take (i + 1)).sum - 1, b * (α.take (i + 1)).sum)) := by
    rw [Finset.disjoint_left]
    rintro p hp hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.1 hq
    rw [Finset.mem_range] at hi hj
    simp only [Prod.mk.injEq] at hji
    have hs : (α.take (j + 1)).sum = (α.take i).sum := Nat.eq_of_mul_eq_mul_left hb hji.2
    have h0 : 0 < (α.take (j + 1)).sum := by
      have := sum_take_lt hpos (show 0 < j + 1 by omega) (show j + 1 ≤ α.length by omega)
      simpa using this
    have hm : 0 < a * (α.take i).sum := Nat.mul_pos ha (hs ▸ h0)
    exact absurd (hs ▸ hji.1) (Nat.ne_of_lt (Nat.sub_lt hm Nat.one_pos))
  rw [compColouring, Finset.card_union_of_disjoint hdisj, h1, h2, two_mul]

/-- **The parts convention of `HJO.Mellit.sweepWitness` is an identity.**
`colourParts c_α = ℓ`: the truncating division of `HJO.Mellit.colourParts` is exact on the
colourings the interface applies `D` to, `c_α` having `2ℓ` cells. Both `0 < a` and the positivity of
the parts are needed — `HJO.Mellit.colourParts_compColouring_a_zero` and
`HJO.Mellit.colourParts_compColouring_zero_part` — and both are hypotheses wherever the interface
reads `D`. -/
theorem colourParts_compColouring {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {α : List ℕ}
    (hpos : ∀ x ∈ α, 0 < x) : colourParts (compColouring a b α) = α.length := by
  rw [colourParts, card_compColouring ha hb hpos, Nat.mul_div_cancel_left _ Nat.zero_lt_two]

/-! ### Where the identities stop

Three `decide`-checked refutations, one per hypothesis of the two theorems above. They are the
reason the hypotheses are there, and the reason `hD` of `HJO.Mellit.rem41_of_sweepComputes` needs
narrowing. -/

/-- **The parts identity fails at a zero part.** At `α = [0]` the cell `(aA_1 - 1, bA_1)` of the
second family is `(0, 0)`, which is the cell `(aA_0, bA_0)` of the first, so `c_α` is a singleton
and `colourParts` reads `0` where `α.length` is `1`.

This is the one corner that is *not* excluded by the hypotheses of
`HJO.Mellit.rem41_of_sweepComputes`, whose `hD` quantifies over every `α` with `α.sum = N`. -/
theorem colourParts_compColouring_zero_part :
    colourParts (compColouring 2 3 [0]) ≠ ([0] : List ℕ).length := by decide

/-- **The parts identity fails at `a = 0`.** The western neighbour `aA_i - 1` is then `aA_i` itself,
so the two families of `HJO.Mellit.compColouring` share their `ℓ - 1` interior cells: at
`α = [1,1]` the colouring has three cells and `colourParts` reads `1` where `α.length` is `2`. -/
theorem colourParts_compColouring_a_zero :
    colourParts (compColouring 0 1 [1, 1]) ≠ ([1, 1] : List ℕ).length := by decide

/-- **The multiplier identity fails at `b = 0`.** Every ordinate of `c_α` is then `0`, and
`HJO.Mellit.colourMult` divides by `b`, so the truncating division reads the multiplier as `0`
whatever `N` is. -/
theorem colourMult_compColouring_b_zero :
    colourMult 0 (compColouring 2 0 [1]) ≠ ([1] : List ℕ).sum := by decide

/-- **The multiplier identity is false on the colouring of a path.** The `(2,3)`-path of height
vector `(0,2,3)` is above-diagonal and coloured `{(0,1), (0,2)}` at the level `21/2` — the
computation of `HJO.Mellit.colouring_east_steps_not_determined` — whose largest ordinate is `2`, so
`HJO.Mellit.colourMult 3` reads `2 / 3 = 0` where `N` is `1`.

So `HJO.Mellit.colourMult` recovers `N` from a colouring of the form `c_α` and from nothing wider:
the cells of `c_η(P̂)` are the ones the level line crosses, and the top of the rectangle need not be
among them. The witness's `D` field is read at `c_α` only, and this is why it must stay that way. -/
theorem colourMult_colouring_ne :
    colourMult 3 (colouring (![0, 2, 3] : Heights 2 3 1) (21 / 2)) ≠ 1 := by
  rw [colouring_east_steps_not_determined.2.2.1]
  decide

/-! ### What the two identities buy

The hypothesis `hD` of `HJO.Mellit.rem41_of_sweepComputes` — that the abstract `D` and `d_-^ℓ` are
`HJO.Mellit.dsc` and the graded lowering run — holds of the witness on the compositions with
positive parts. -/

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`d_-^ℓ` on the grading `ℓ` is `HJO.Mellit.lowerRun q ℓ` on the grading `0`.** The degreewise
lowering operator of the witness applies `HJO.Sweep.dminus q k` on the `k`-th grading and moves to
the `(k-1)`-st, so `ℓ` applications starting at the grading `ℓ` read the indices `ℓ, ℓ-1, …, 1` in
that order and land on the grading `0` — which is exactly the composite `HJO.Sweep.dminus` gives
`d_-^ℓ`, and exactly why `HJO.Mellit.colourParts` has to return `ℓ`: from any other grading the run
would read the wrong indices and would not reach `V_0`. -/
theorem gradedOp_dminus_pow (q : L) (ℓ : ℕ) (F : Total L) :
    ((gradedOp (fun k => dminus q k) (fun k => k - 1)) ^ ℓ) (gradedIn L ℓ F)
      = gradedIn L 0 (lowerRun q ℓ F) := by
  induction ℓ generalizing F with
  | zero => rw [pow_zero, lowerRun]; rfl
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, gradedOp_apply, Nat.add_sub_cancel, ih, lowerRun,
        Module.End.mul_apply]

/-- The witness's `proj` on the grading `0` is the reading `V_0 = Λ` by the constant coefficient. -/
theorem sweepWitness_proj_gradedIn (q u : L) (a b : ℕ) (G : Total L) :
    (sweepWitness q u a b).proj (gradedIn L 0 G) = MvPolynomial.constantCoeff G := by
  change MvPolynomial.lcoeff (Sym.Lambda L) 0
      (DirectSum.component L ℕ (fun _ : ℕ => Total L) 0 (gradedIn L 0 G)) = _
  rw [gradedIn, DirectSum.component.lof_self]
  rfl

/-- **The witness satisfies `hD` on the compositions with positive parts.**
`proj (d_-^ℓ D_{η,c_α}) = constantCoeff (lowerRun q ℓ (D_{η,c_α}))` with the right `N`: this is the
hypothesis `hD` of `HJO.Mellit.rem41_of_sweepComputes`, and with it that theorem reduces
`HJO.Mellit.Rem41` for `HJO.Mellit.sweepWitness` to `HJO.Mellit.SweepComputes` alone.

The two conventions are what the proof spends: `HJO.Mellit.colourParts_compColouring` puts
`D_{η,c_α}` in the grading `ℓ`, so that `HJO.Mellit.gradedOp_dminus_pow` reads the indices
`ℓ, …, 1` and lands on the grading `0` where `proj` is the constant coefficient, and
`HJO.Mellit.colourMult_compColouring` makes the multiplier `HJO.Mellit.dsc` is called at the `N` of
the clause.

`hD` as stated in `HJO.Mellit.rem41_of_sweepComputes` quantifies over every `α` of sum `N`, and
that version is false of the witness by
`HJO.Mellit.colourParts_compColouring_zero_part`; the positivity hypothesis here is exactly the
difference, and it is available at the one place that theorem's proof uses `hD`. -/
theorem sweepWitness_proj_dminus_pow_D (q u : L) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (N : ℕ)
    (η : ℚ) {α : List ℕ} (hpos : ∀ x ∈ α, 0 < x) (hsum : α.sum = N) :
    (sweepWitness q u a b).proj
        (((sweepWitness q u a b).dminus ^ α.length)
          ((sweepWitness q u a b).D η (compColouring a b α)))
      = MvPolynomial.constantCoeff
          (lowerRun q α.length (dsc q u a b N η (compColouring a b α))) := by
  have hD : (sweepWitness q u a b).D η (compColouring a b α)
      = gradedIn L α.length (dsc q u a b N η (compColouring a b α)) := by
    change gradedIn L (colourParts (compColouring a b α))
        (dsc q u a b (colourMult b (compColouring a b α)) η (compColouring a b α)) = _
    rw [colourParts_compColouring ha hb hpos, colourMult_compColouring hb, hsum]
  rw [hD]
  change (sweepWitness q u a b).proj
      (((gradedOp (fun k => dminus q k) (fun k => k - 1)) ^ α.length) _) = _
  rw [gradedOp_dminus_pow, sweepWitness_proj_gradedIn]

end HJO.Mellit
