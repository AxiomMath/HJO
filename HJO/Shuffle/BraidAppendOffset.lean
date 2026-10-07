/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidIndexRelabel
public import HJO.Shuffle.BraidPositionWindow
public meta import HJO.Attr

/-! # The offset of the appended entry, and the order of the components

`HJO.Mellit.fract_crossingAbscissa_eq_levelPosition` computes every position of a colouring's
special-braid data as a rank measured up from the level,
`v_i = \theta(\widehat{rk}(w_i) - \eta)/(a(aN+1)N)`. For the colouring of an above-diagonal path of
return composition `\alpha` the crossed east step of the `i`-th component is known explicitly — it
is the western neighbour `(aA_{i+1} - 1, bA_{i+1})` of the `(i+1)`-st diagonal touch point, by
`HJO.Mellit.colStep_colouringEast_hasAboveReturns` — and its rank is therefore explicit too:

```
rk(aA - 1, bA) = (aN+1)N(a·bA - b·(aA - 1)) + (aA - 1) = b(aN+1)N + aA - 1.
```

So the whole position is explicit. Writing `D := a(aN+1)N + b(aN+1)N - 1` and using
`\theta D = a(aN+1)N`, the normalisation collapses to a single division and

```
v_i = (b(aN+1)N + aA_{i+1} - 1 - \eta) / D.
```

Two things follow at once, and they are the two hypotheses of
`HJO.Mellit.braidRep_specialBraid_dplusIter` this file is for.

## Main results

* `HJO.Mellit.braidDataOfColouring_fst_hasAboveReturns` — the display above: the position of the
  `i`-th component of the colouring of a composition path, in closed form.
* `HJO.Mellit.appendOffset` and `HJO.Mellit.braidDataOfColouring_fst_last_succ_eq` — **the value of
  the offset `\delta`**. The last component has `A_\ell = N`, so its position is
  `(b(aN+1)N + aN - 1 - \eta)/D`, which is exactly `1 - \theta - \delta` for
  `\delta = (\eta - aN)/D`, of which `HJO.Mellit.braidDataOfColouring_fst_last_succ_ne` gives only
  `\delta \ne 0`. This discharges the `hw₀` of `HJO.Mellit.sweepIn_braidRep_specialBraid` rather
  than leaving it as a hypothesis.
* `HJO.Mellit.braidDataOfColouring_fst_castSucc_lt_last` — **`hstart`**: the appended component
  stands strictly above every other. The positions are an increasing function of `A_{i+1}`, and
  `A_{i+1} < A_\ell = N` for every earlier component, so this is the partial sums of a composition
  with positive parts increasing. It is a comparison *between* components, which the
  position-as-rank formula makes trivial and nothing before it could make at all.
* `HJO.Mellit.sweepIn_braidRep_specialBraid_rotateLast_appendOffset` — the append clause with `hw₀`
  and `hstart` discharged on top of the `hdata` and `hβ` of
  `HJO.Mellit.sweepIn_braidRep_specialBraid_rotateLast`. Four of the seven hypotheses of
  `HJO.Mellit.braidRep_specialBraid_dplusIter` are now proved for the composition colouring; three
  remain: `HJO.Braid.IsAppendSetup`, `hgap`, `hmove`. All three are discharged downstream —
  `hgap` in `HJO/Shuffle/BraidAppendGrid.lean` and the other two in
  `HJO/Shuffle/BraidAppendCluster.lean`, whose
  `HJO.Mellit.sweepIn_braidRep_specialBraid_appendFinalTuple` carries none of them.

Two smaller gains fall out of the same computation:

* `HJO.Mellit.fract_crossingAbscissa_componentTopIndex_last_lt'` — the strict inequality of
  `HJO.Mellit.fract_crossingAbscissa_componentTopIndex_last_lt` **without** its `a \le b`
  hypothesis. The value makes the sign of the gap visible, so the bound on `\eta` that hypothesis
  was placing is not needed.
* `HJO.Mellit.appendOffset_sepLevel` — at `HJO.Mellit.sepLevel`, `\delta = 1/(2D)` exactly, which is
  the `\delta \le 1/n` of `HJO.Braid.gap_of_grid` at `n = 2D`. This is the arithmetic half of what
  `hgap` will need; the grid clause itself is
  `HJO.Mellit.exists_int_braidDataOfColouring_fst_mul_gridDen` in
  `HJO/Shuffle/BraidAppendGrid.lean`.

Nothing in this file mentions `q`, `u`, a field or a representation outside the final corollary,
which merely re-exports the one of `HJO/Shuffle/BraidIndexRelabel.lean`. The hypotheses are the
colouring's standing ones — `0 < a`, `0 < b`, `0 < N`, `Nat.Coprime a b`, `\eta` admissible and
separating with `\eta > aN`, `HJO.Mellit.HasAboveReturns` — and `a \le b` is used nowhere.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid

variable {a b N : ℕ}

/-! ### The rank span `D`, and what it does to the normalisation -/

/-- **`\theta D = a(aN+1)N`**, where `D = a(aN+1)N + b(aN+1)N - 1` is the span of one period of the
rank along the level line. This is `HJO.Mellit.rankDen_mul_sweepSlope` (`a(aN+1)N·s = b(aN+1)N - 1`,
so `D = a(aN+1)N·(1+s)`) followed by `HJO.Mellit.sweepTheta_mul` (`\theta(s+1) = 1`). -/
theorem sweepTheta_mul_rankSpan (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    sweepTheta a b N * ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1)
      = (a : ℚ) * ((a : ℚ) * N + 1) * N := by
  have h1 := rankDen_mul_sweepSlope (a := a) (b := b) (N := N) ha hN
  have h2 := sweepTheta_mul (a := a) (b := b) (N := N) (one_add_sweepSlope_pos ha hb hN).ne'
  have hsplit : (a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1
      = ((a : ℚ) * ((a : ℚ) * N + 1) * N) * (sweepSlope a b N + 1) := by
    linear_combination -h1
  rw [hsplit, show sweepTheta a b N * (((a : ℚ) * ((a : ℚ) * N + 1) * N) * (sweepSlope a b N + 1))
    = ((a : ℚ) * ((a : ℚ) * N + 1) * N) * (sweepTheta a b N * (sweepSlope a b N + 1)) from by ring,
    h2, mul_one]

/-- The rank span is positive: `a(aN+1)N \ge 2` already on a rectangle with a row and a column. -/
theorem rankSpan_pos (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    (0 : ℚ) < (a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1 := by
  have ha' : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
  have hb' : (1 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
  have hN' : (1 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN
  have haN : (1 : ℚ) ≤ (a : ℚ) * N := by nlinarith
  have hbN : (1 : ℚ) ≤ (b : ℚ) * N := by nlinarith
  rw [show (a : ℚ) * ((a : ℚ) * N + 1) * N = ((a : ℚ) * N) * ((a : ℚ) * N + 1) from by ring,
    show (b : ℚ) * ((a : ℚ) * N + 1) * N = ((b : ℚ) * N) * ((a : ℚ) * N + 1) from by ring]
  nlinarith

/-- **The normalisation of `HJO.Mellit.levelPosition` collapses to a single division by `D`.** Since
`\theta D = a(aN+1)N`, the two-step scaling `\theta·(r - \eta)/(a(aN+1)N)` is just
`(r - \eta)/D`: a rank measured up from the level, divided by the span of one period. -/
theorem levelPosition_eq_div_rankSpan (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (η r : ℚ) :
    levelPosition a b N η r = (r - η) /
      ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1) := by
  have hM := rankDen_pos (a := a) (N := N) ha hN
  have hD := rankSpan_pos (a := a) (b := b) (N := N) ha hb hN
  rw [levelPosition, eq_div_iff hD.ne',
    show sweepTheta a b N * ((r - η) / ((a : ℚ) * ((a : ℚ) * N + 1) * N)) *
        ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1)
      = (sweepTheta a b N *
          ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1)) *
        ((r - η) / ((a : ℚ) * ((a : ℚ) * N + 1) * N)) from by ring,
    sweepTheta_mul_rankSpan ha hb hN]
  field_simp

/-! ### The rank of the crossed east step of a component -/

/-- **The rank of the western neighbour of a diagonal touch point.** `HJO.Mellit.abovePointRank` is
`(aN+1)N(ay - bx) + x`, and at `(aA - 1, bA)` the bracket is `abA - b(aA - 1) = b` whatever `A` is,
so the rank is `b(aN+1)N + aA - 1`. The truncated subtraction is harmless for `A \ge 1`. -/
theorem cast_pointRank_eastStep (a b N A : ℕ) (ha : 0 < a) (hA : 0 < A) :
    ((pointRank a b N (a * A - 1, b * A) : ℤ) : ℚ)
      = (b : ℚ) * ((a : ℚ) * N + 1) * N + (a : ℚ) * A - 1 := by
  have h1 : 1 ≤ a * A := Nat.one_le_iff_ne_zero.2 (by positivity)
  rw [pointRank, abovePointRank]
  push_cast [Nat.cast_sub h1]
  ring

/-! ### The positions of a composition colouring, in closed form -/

/-- **THE POSITION OF THE `i`-TH COMPONENT OF A COMPOSITION COLOURING.** For an above-diagonal path
of return composition `\alpha` and a separating admissible level `\eta > aN`,

```
v_i = (b(aN+1)N + aA_{i+1} - 1 - \eta) / D,      A_{i+1} = \alpha_1 + \cdots + \alpha_{i+1},
```

with `D = a(aN+1)N + b(aN+1)N - 1`.

This is `HJO.Mellit.fract_crossingAbscissa_eq_levelPosition` — the position is a normalised rank —
evaluated at the crossed east
step `HJO.Mellit.colStep_colouringEast_hasAboveReturns` names. Every dependence on the path beyond
its return composition has disappeared: the position of a component is a function of the partial sum
alone, which is what makes both the value of the append offset and the order of the components
computable. -/
theorem braidDataOfColouring_fst_hasAboveReturns (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : Nat.Coprime a b) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hηN : ((a * N : ℕ) : ℚ) < η) {α : List ℕ}
    {y : Heights a b N} (hret : HasAboveReturns α y) {k : ℕ} (i : Fin k)
    (hi : (i : ℕ) < α.length) :
    (braidDataOfColouring a b N y η k).1 i
      = ((b : ℚ) * ((a : ℚ) * N + 1) * N + (a : ℚ) * ((α.take ((i : ℕ) + 1)).sum : ℕ) - 1 - η) /
        ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1) := by
  have hηpos : 0 < η := lt_of_le_of_lt (Nat.cast_nonneg _) hηN
  have hcardE := card_colouringEast_hasAboveReturns hηa hηs hab ha hb hN hηN hret
  have hiE : (i : ℕ) < #(colouringEast y η) := by omega
  have hApos : 0 < (α.take ((i : ℕ) + 1)).sum := by
    have := sum_take_lt hret.2.1 (show 0 < (i : ℕ) + 1 by omega) (show (i : ℕ) + 1 ≤ α.length by
      omega)
    simpa using this
  rw [braidDataOfColouring_fst_eq_levelPosition ha hb hN hηa hηpos i hiE,
    colStep_colouringEast_hasAboveReturns hηa hηs hab ha hb hN hηN hret hi,
    levelPosition_eq_div_rankSpan ha hb hN, cast_pointRank_eastStep a b N _ ha hApos]

/-! ### The value of the offset `δ` -/

/-- **The offset of the appended entry**: `\delta = (\eta - aN)/D` with
`D = a(aN+1)N + b(aN+1)N - 1`.

This is the `\delta` of `HJO.Braid.IsAppendSetup` — the amount by which the appended entry of the
special-braid data of a composition colouring sits *below* `1 - \theta` — and not the
inversion-count defect that forces the `\sqrt q` extension elsewhere. -/
noncomputable def appendOffset (a b N : ℕ) (η : ℚ) : ℚ :=
  (η - (a : ℚ) * N) /
    ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1)

/-- **The offset is strictly positive** at every separating admissible level, every such level
having `\eta > aN`. This strengthens `HJO.Mellit.braidDataOfColouring_fst_last_succ_ne` — the
appended entry is never `1 - \theta` — by attaching the size of the gap. -/
theorem appendOffset_pos (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hηN : ((a * N : ℕ) : ℚ) < η) : 0 < appendOffset a b N η := by
  have hD := rankSpan_pos (a := a) (b := b) (N := N) ha hb hN
  have hηq : (a : ℚ) * N < η := by push_cast at hηN; exact hηN
  exact div_pos (by linarith) hD

/-- `1 - \theta - \delta` in the same single-division shape as
`HJO.Mellit.braidDataOfColouring_fst_hasAboveReturns`: subtracting `\theta = a(aN+1)N/D` from `1`
leaves `(b(aN+1)N - 1)/D`, and a further `\delta` leaves `(b(aN+1)N + aN - 1 - \eta)/D`. -/
theorem one_sub_sweepTheta_sub_appendOffset (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (η : ℚ) :
    1 - sweepTheta a b N - appendOffset a b N η
      = ((b : ℚ) * ((a : ℚ) * N + 1) * N + (a : ℚ) * N - 1 - η) /
        ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1) := by
  have hD := rankSpan_pos (a := a) (b := b) (N := N) ha hb hN
  have hθ := sweepTheta_mul_rankSpan (a := a) (b := b) (N := N) ha hb hN
  have hδ : appendOffset a b N η *
      ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1)
      = η - (a : ℚ) * N := by
    rw [appendOffset]; exact div_mul_cancel₀ _ hD.ne'
  rw [eq_div_iff hD.ne']
  linear_combination -hθ - hδ

/-- **THE VALUE OF `δ`, AS A STATEMENT.** The position the colouring of an above-diagonal path of
return composition `\alpha` gives its **last** component — the index `HJO.Braid.rotateLast` rotates
to `0`, so the one `HJO.Mellit.braidRep_specialBraid_dplusIter`'s `hw₀` reads — is

```
v_\ell = 1 - \theta - \frac{\eta - aN}{a(aN+1)N + b(aN+1)N - 1}.
```

The last component's crossed east step is `(aN - 1, bN)`, the last east step of the path, since
`A_\ell = \alpha_1 + \cdots + \alpha_\ell = N`; its rank is `b(aN+1)N + aN - 1` by
`HJO.Mellit.cast_pointRank_eastStep`, and
`HJO.Mellit.braidDataOfColouring_fst_hasAboveReturns` divides that by `D`.

Together with `HJO.Mellit.appendOffset_pos` this **discharges** the
`hw₀ : w_0 = 1 - \theta - \delta` of `HJO.Mellit.sweepIn_braidRep_specialBraid` at
`\delta = HJO.Mellit.appendOffset`, where
`HJO.Mellit.braidDataOfColouring_fst_last_succ_ne` gives only `\delta \ne 0`. It needs no
`a \le b`. -/
theorem braidDataOfColouring_fst_last_succ_eq (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : Nat.Coprime a b) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hηN : ((a * N : ℕ) : ℚ) < η) {α : List ℕ}
    {y : Heights a b N} (hret : HasAboveReturns α y) {k : ℕ} (hlen : α.length = k + 1) :
    (braidDataOfColouring a b N y η (k + 1)).1 (Fin.last k)
      = 1 - sweepTheta a b N - appendOffset a b N η := by
  rw [braidDataOfColouring_fst_hasAboveReturns ha hb hN hab hηa hηs hηN hret (Fin.last k)
      (by rw [Fin.val_last]; omega),
    one_sub_sweepTheta_sub_appendOffset ha hb hN]
  rw [Fin.val_last, show k + 1 = α.length from hlen.symm, List.take_length, hret.2.2.1]

/-- **The strict inequality of
`HJO.Mellit.fract_crossingAbscissa_componentTopIndex_last_lt` without its `a \le b`.** Once the gap
is a *value* rather than a sign, `\eta > aN` is the whole of what makes it positive; the bound on
`\eta` that `a \le b` was supplying is not needed. -/
theorem fract_crossingAbscissa_componentTopIndex_last_lt' (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : Nat.Coprime a b) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hηN : ((a * N : ℕ) : ℚ) < η) {α : List ℕ}
    {y : Heights a b N} (hret : HasAboveReturns α y) (hα : α ≠ []) :
    Int.fract (crossingAbscissa a b N η (componentTopIndex a b N y η (α.length - 1)))
      < 1 - sweepTheta a b N := by
  have hpos : 0 < α.length := List.length_pos_of_ne_nil hα
  have h := braidDataOfColouring_fst_last_succ_eq (k := α.length - 1) ha hb hN hab hηa hηs hηN hret
    (by omega)
  rw [braidDataOfColouring_fst, Fin.val_last] at h
  rw [h]
  linarith [appendOffset_pos (a := a) (b := b) (N := N) ha hb hN hηN]

/-! ### The appended component stands above all the others -/

/-- **THE ORDER OF THE COMPONENTS IS THE ORDER OF THEIR PARTIAL SUMS.** By
`HJO.Mellit.braidDataOfColouring_fst_hasAboveReturns` the position of the `i`-th component is an
increasing affine function of `A_{i+1}`, and the partial sums of a composition with positive parts
increase strictly. -/
theorem braidDataOfColouring_fst_lt_of_lt (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : Nat.Coprime a b) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hηN : ((a * N : ℕ) : ℚ) < η) {α : List ℕ}
    {y : Heights a b N} (hret : HasAboveReturns α y) {k : ℕ} (i j : Fin k)
    (hij : (i : ℕ) < (j : ℕ)) (hj : (j : ℕ) < α.length) :
    (braidDataOfColouring a b N y η k).1 i < (braidDataOfColouring a b N y η k).1 j := by
  have hD := rankSpan_pos (a := a) (b := b) (N := N) ha hb hN
  have ha' : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha
  have hsum : (α.take ((i : ℕ) + 1)).sum < (α.take ((j : ℕ) + 1)).sum :=
    sum_take_lt hret.2.1 (by omega) (by omega)
  have hsumq : (((α.take ((i : ℕ) + 1)).sum : ℕ) : ℚ) < (((α.take ((j : ℕ) + 1)).sum : ℕ) : ℚ) := by
    exact_mod_cast hsum
  rw [braidDataOfColouring_fst_hasAboveReturns ha hb hN hab hηa hηs hηN hret i (by omega),
    braidDataOfColouring_fst_hasAboveReturns ha hb hN hab hηa hηs hηN hret j hj,
    div_lt_div_iff_of_pos_right hD]
  nlinarith

/-- **`hstart`: THE APPENDED COMPONENT IS ABOVE ALL THE OTHERS.** Every component but the last has
`A_{i+1} < A_\ell = N`, so `HJO.Mellit.braidDataOfColouring_fst_lt_of_lt` puts its position strictly
below the last one's. This is the `hstart : \forall t, w_{t.succ} < w_0` of
`HJO.Mellit.sweepIn_braidRep_specialBraid`, read at the colouring's own indices through
`HJO.Braid.rotateLast`.

It is a comparison *between* components of the colouring. Nothing that reads one position at a time
can make it; what makes it is that every position is a normalised rank
(`HJO.Mellit.fract_crossingAbscissa_eq_levelPosition`), so the order of the positions on the circle
is the order of the ranks, and here the ranks are explicit. -/
theorem braidDataOfColouring_fst_castSucc_lt_last (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : Nat.Coprime a b) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hηN : ((a * N : ℕ) : ℚ) < η) {α : List ℕ}
    {y : Heights a b N} (hret : HasAboveReturns α y) {k : ℕ} (hlen : α.length = k + 1)
    (t : Fin k) :
    (braidDataOfColouring a b N y η (k + 1)).1 t.castSucc
      < (braidDataOfColouring a b N y η (k + 1)).1 (Fin.last k) :=
  braidDataOfColouring_fst_lt_of_lt ha hb hN hab hηa hηs hηN hret t.castSucc (Fin.last k)
    (by rw [Fin.val_castSucc, Fin.val_last]; omega) (by rw [Fin.val_last]; omega)

/-! ### At the separating level the offset is exactly one grid step -/

/-- **`\delta = 1/(2D)` at `HJO.Mellit.sepLevel`.** `HJO.Braid.gap_of_grid` discharges the isotopy
clause of `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs` from a `1/n`-grid as soon as
`\delta \le 1/n`; the grid the positions of a colouring lie on is `1/(2D)`, every position being
`HJO.Mellit.braidDataOfColouring_fst_hasAboveReturns` with a half-integer `\eta`. At
`\eta = aN + 1/2` the offset is exactly that step, so the boundary case of
`HJO.Braid.gap_of_grid` is the live one. The grid clause itself is proved in
`HJO/Shuffle/BraidAppendGrid.lean`. -/
theorem appendOffset_sepLevel (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    appendOffset a b N (sepLevel a N) *
        (2 * ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1)) = 1 := by
  have hD := rankSpan_pos (a := a) (b := b) (N := N) ha hb hN
  have hhalf : sepLevel a N - (a : ℚ) * N = 1 / 2 := by rw [sepLevel]; ring
  rw [appendOffset, hhalf, div_mul_eq_mul_div,
    show (1 : ℚ) / 2 * (2 * ((a : ℚ) * ((a : ℚ) * N + 1) * N
        + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1))
      = (a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1 from by ring,
    div_self hD.ne']

/-! ### The value checked against an explicit instance -/

/-- **The offset at the witness of `HJO.Mellit.hasAboveReturns_example`**: for `(a,b,N) = (2,3,2)`
and `\eta = aN + 1/2 = 9/2`, the span is `D = 20 + 30 - 1 = 49` and `\delta = (1/2)/49 = 1/98`. -/
theorem appendOffset_example : appendOffset 2 3 2 (sepLevel 2 2) = 1 / 98 := by
  rw [appendOffset, sepLevel]
  norm_num

/-- **The general value agrees with an independently computed instance.**
`HJO.Mellit.fract_crossingAbscissa_componentTopIndex_last_example` evaluates the position of the
last component of the `(4,6)`-path of heights `(0,3,3,6,6)` at `\eta = 9/2` to `57/98` by unfolding
`HJO.Mellit.crossingAbscissa` and `Int.fract` directly. Here the same number is produced by
`HJO.Mellit.braidDataOfColouring_fst_last_succ_eq` from the closed form, and
`1 - \theta - \delta = 29/49 - 1/98 = 57/98`.

So the closed form `\delta = (\eta - aN)/D` is not merely consistent with
`HJO.Mellit.braidDataOfColouring_fst_last_succ_ne`: it reproduces the number computed in
`HJO.Mellit.fract_crossingAbscissa_componentTopIndex_last_example`. -/
theorem braidDataOfColouring_fst_last_succ_eq_example :
    (braidDataOfColouring 2 3 2 (![0, 3, 3, 6, 6] : Heights 2 3 2) (sepLevel 2 2) 2).1
        (Fin.last 1) = 57 / 98 := by
  rw [braidDataOfColouring_fst_last_succ_eq (a := 2) (b := 3) (N := 2) (k := 1) (by norm_num)
      (by norm_num) (by norm_num) (by decide) (isAdmissibleLevel_sepLevel 2 2)
      (separatesDiagonal_sepLevel (by norm_num)) (by rw [sepLevel]; norm_num)
      hasAboveReturns_example (by norm_num),
    appendOffset_example, sweepTheta, sweepSlope]
  norm_num

/-- The witness's own value, read back off
`HJO.Mellit.fract_crossingAbscissa_componentTopIndex_last_example`: the two routes to the last
component's position agree on the nose. -/
theorem braidDataOfColouring_fst_last_succ_eq_example' :
    (braidDataOfColouring 2 3 2 (![0, 3, 3, 6, 6] : Heights 2 3 2) (sepLevel 2 2) 2).1
        (Fin.last 1)
      = Int.fract (crossingAbscissa 2 3 2 (sepLevel 2 2)
          (componentTopIndex 2 3 2 (![0, 3, 3, 6, 6] : Heights 2 3 2) (sepLevel 2 2) 1)) := by
  rw [braidDataOfColouring_fst_last_succ_eq_example,
    fract_crossingAbscissa_componentTopIndex_last_example.1]

/-! ### The append clause with `hw₀` and `hstart` discharged -/

section AppendAtLast

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`HJO.Mellit.braidRep_specialBraid_dplusIter` at the composition colouring, with four of its
seven hypotheses proved.** On top of the `hdata` and `hβ` that
`HJO.Mellit.sweepIn_braidRep_specialBraid_rotateLast` discharges,
`hw₀` is now `HJO.Mellit.braidDataOfColouring_fst_last_succ_eq` at
`\delta = HJO.Mellit.appendOffset` and `hstart` is
`HJO.Mellit.braidDataOfColouring_fst_castSucc_lt_last`.

Three hypotheses remain: `HJO.Braid.IsAppendSetup` at the offset's *value*, the isotopy clause
`hgap`, and `hmove`. -/
theorem sweepIn_braidRep_specialBraid_rotateLast_appendOffset {q u r : L} {k : ℕ} {e : ℚ}
    {w : Fin (k + 1) → ℚ} {η : ℚ} {y : Heights a b N} {α : List ℕ}
    (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q)
    {Ω : ℕ → ℕ → ℕ → ((sweepWitness q u a b).W →ₗ[L] (sweepWitness q u a b).W)}
    (hΩ : IsReplicationFamily (sweepWitness q u a b) Ω)
    (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hab : Nat.Coprime a b)
    (hηa : IsAdmissibleLevel η) (hηs : SeparatesDiagonal a b N η)
    (hηN : ((a * N : ℕ) : ℚ) < η) (hret : HasAboveReturns α y) (hlen : α.length = k + 1)
    (hα : α ≠ [])
    (H : IsAppendSetup a b (α.getLast hα) k e (appendOffset a b N η) (sweepTheta a b N) w)
    (hgap : ∀ (t : Fin k) (i : ℕ),
      i + 1 < (braidDataOfColouring a b N y η (k + 1)).2 t.castSucc →
      (nextCrossing (sweepTheta a b N))^[i]
          ((braidDataOfColouring a b N y η (k + 1)).1 t.castSucc) <
        (braidDataOfColouring a b N y η (k + 1)).1 (Fin.last k) + sweepTheta a b N)
    (hmove : moveTuple (sweepTheta a b N)
      ((braidDataOfColouring a b N y η (k + 1)).1 ∘ rotateLast k)
      ((specialMoveList ((braidDataOfColouring a b N y η (k + 1)).2 ∘ Fin.castSucc)).map
        Fin.succ) = w) :
    sweepIn q u a b (k + 1)
        ((braidRepMellit q u hq hq1 hqp hr (k + 1)
            (specialBraid (sweepTheta a b N) (braidDataOfColouring a b N y η (k + 1)).1
              (braidDataOfColouring a b N y η (k + 1)).2)
          (dplusIterPiece q (k + 1)) : pieceSub L (k + 1)) : Total L)
      = ((-1 : L) ^ ((a - 1) * α.getLast hα) * (q * u) ^ (1 - (α.getLast hα : ℤ))) •
          stage (sweepWitness q u a b) Ω a b k (α.getLast hα) (sweepIn q u a b k
            ((braidRepMellit q u hq hq1 hqp hr k
                (specialBraid (sweepTheta a b N) (braidDataOfColouring a b N y η k).1
                  (braidDataOfColouring a b N y η k).2)
              (dplusIterPiece q k) : pieceSub L k) : Total L)) :=
  sweepIn_braidRep_specialBraid_rotateLast hq hq1 hqp hr hΩ ha hb hN hab hηa hηs hηN hret hlen hα H
    (braidDataOfColouring_fst_last_succ_eq ha hb hN hab hηa hηs hηN hret hlen) hgap
    (braidDataOfColouring_fst_castSucc_lt_last ha hb hN hab hηa hηs hηN hret hlen) hmove

end AppendAtLast

end HJO.Mellit

end
