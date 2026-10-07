/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitThm58Iteration

/-! # The level iteration above a floor, and what the floor costs

`HJO.Mellit.agreesWithDsc_of_recursions` asks its candidate for the four recursion clauses at
*every* pair of admissible levels. `HJO.Mellit.braidValueColouring` cannot supply that:
`HJO.Mellit.not_braid_recursions_two_three_one` refutes the conjunction of
`HJO.Mellit.SweepRecursionACD`, `HJO.Mellit.SweepRecursionBE` and `HJO.Mellit.SweepRecursionUnswept`
for it at `(a, b, N) = (2, 3, 1)`, and the mechanism is a level below the rank `0`, where the braid
candidate is the vacuum (`HJO.Mellit.braidValueColouring_eq_one_of_lt_zero`) and `HJO.Mellit.dsc` is
not (`HJO.Mellit.dsc_two_three_one_below_zero_ne_one`). Every per-event braid clause proved in the
library excludes exactly that region by a level floor `aN < ηlo`.

This file restates the clauses with that floor and reproves the iteration above it.

## The floor is free, and this is the reason

The induction of `HJO.Mellit.agreesWithDsc_of_recursions` runs **upward**. Its measure
`HJO.Mellit.ranksAbove` is the set of ranks of the rectangle above the level; it is empty at the top
and the base case is there, and the inductive step at a level `η` with something still above it
takes the *least* rank `r` above `η` and appeals to the level `r + 1/2`, which is higher. So every
level the chain from `η` visits is `≥ η`, and a floor on the starting level is inherited by the
whole chain. `HJO.Mellit.agreesWithDsc_of_recursions_floor` is that statement: the floored clauses
deliver agreement with `HJO.Mellit.dsc` at every admissible level above `aN`.

Two things drop out. First, **every level used downstream is inside the floored region.**
`HJO.Mellit.MellitInduction` — the `hind` binder of `HJO.Mellit.shuffle_of_lhs_and_induction` —
quantifies over the admissible levels that separate the diagonal, and
`HJO.Mellit.lt_of_separatesDiagonal` proves every such level is above `aN`: the corner `(aN, bN)`
lies on the diagonal and has rank exactly `aN`, so `HJO.Mellit.SeparatesDiagonal` forces `aN ≤ η`
and admissibility makes it strict. So the floor is not an extra hypothesis a user of the result must
supply, it is a consequence of one the user already has, and
`HJO.Mellit.eq_dsc_of_recursions_separatesDiagonal` settles every level `hind` reads —
`HJO.Mellit.eq_dsc_sepLevel_floor` at `HJO.Mellit.sepLevel a N = aN + 1/2` being one case of it.
Second, the **origin clause is no longer needed**. The origin has rank
`0`, so `HJO.Mellit.Isolates a b N 0 0 ηlo ηhi` forces `ηlo < 0`, which the floor `0 ≤ aN < ηlo`
refutes (`HJO.Mellit.ne_origin_of_floor`). The floored principle therefore carries **four**
hypotheses where the unfloored one carries five: `HJO.Mellit.SweepRecursionBOrigin` is not among
them. That is a strict improvement, and it is the reason the floor is worth having independently of
the braid.

## What the floor does NOT buy, and this is the load-bearing warning

The chain the iteration walks is **not** a chain of consecutive levels. From `ηlo = m + 1/2` it
jumps to `r + 1/2` where `r` is the least rank of the rectangle above `ηlo`, and `r` need not be
`m + 1`: most integers are not ranks. `HJO/Shuffle/MellitFloorStepGap.lean` computes this at
`(a, b, N) = (2, 3, 1)`, where every rank is even, so from the admissible above-floor level `9/2`
every isolating pair has `ηhi > 9/2 + 1`.

This matters because the type-`D` braid clause
(`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_D_of_step`) carries
`ηhi ≤ ηlo + 1` on top of the floor. `HJO.Mellit.SweepRecursionACDFloorStep` below is the clause
with that restriction added, and it is the one the braid discharges
(`HJO.Mellit.braidValueColouring_sweepRecursionACDFloorStep`); the iteration proved here consumes
`HJO.Mellit.SweepRecursionACDFloor`, without it. **The floor is free and the step restriction is
not.** Nothing here claims the step restriction is fatal — only that the two statements are
different and the gap between them is what the braid route still has to close.

No genericity is spent. Every inverse sits inside the clauses carried as hypotheses on `R`; the
theorems below hold at every `q` and `u` in a field, with `0 < a`, `0 < b`, `0 < N` the only
arithmetic hypotheses, exactly as in `HJO/Shuffle/MellitThm58Iteration.lean`.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {a b N : ℕ}

/-! ### The clauses above a floor -/

/-- **The `A`/`C`/`D` clause of Mellit's Theorem 4.2 above the floor `aN`.** Verbatim
`HJO.Mellit.SweepRecursionACD` with the single hypothesis `aN < ηlo` inserted — which is exactly
what `HJO.Mellit.sweepRecursionACDFloor_of_sweepRecursionACD` checks, its proof discarding that one
hypothesis and nothing else. -/
def SweepRecursionACDFloor (q u : L) (a b N : ℕ) (R : ℚ → Finset (ℕ × ℕ) → Total L) : Prop :=
  ∀ (X Y : ℕ) (ηlo ηhi : ℚ), ((a * N : ℕ) : ℚ) < ηlo → Isolates a b N X Y ηlo ηhi →
    ∀ y : Heights a b N, IsAboveDiagonal y → (X, Y) ∈ sweptRegion y →
      (ht y X < Y ∨ ht y (X + 1) = Y) →
        R ηlo (colouring y ηlo) = sweepOperator q u y (X, Y) (R ηhi (colouring y ηhi))

/-- **The `A`/`C`/`D` clause above the floor and at consecutive levels only.** This is
`HJO.Mellit.SweepRecursionACDFloor` with `ηhi = ηlo + 1` added, the restriction the type-`D`
braid clause carries.

It is stated here, next to the clause the iteration actually consumes, so that the difference is
visible in one place: `HJO.Mellit.braidValueColouring_sweepRecursionACDFloorStep` discharges *this*
one, and `HJO.Mellit.agreesWithDsc_of_recursions_floor` asks for the other. -/
def SweepRecursionACDFloorStep (q u : L) (a b N : ℕ) (R : ℚ → Finset (ℕ × ℕ) → Total L) : Prop :=
  ∀ (X Y : ℕ) (ηlo ηhi : ℚ), ((a * N : ℕ) : ℚ) < ηlo → ηhi = ηlo + 1 →
    Isolates a b N X Y ηlo ηhi →
    ∀ y : Heights a b N, IsAboveDiagonal y → (X, Y) ∈ sweptRegion y →
      (ht y X < Y ∨ ht y (X + 1) = Y) →
        R ηlo (colouring y ηlo) = sweepOperator q u y (X, Y) (R ηhi (colouring y ηhi))

/-- **The `BE` clause of Mellit's Theorem 4.2 above the floor `aN`**, verbatim
`HJO.Mellit.SweepRecursionBE` with `aN < ηlo` inserted. -/
def SweepRecursionBEFloor (q u : L) (a b N : ℕ) (R : ℚ → Finset (ℕ × ℕ) → Total L) : Prop :=
  ∀ (P : ℕ × ℕ) (ηlo ηhi : ℚ), ((a * N : ℕ) : ℚ) < ηlo →
    IsAdmissibleLevel ηlo → IsAdmissibleLevel ηhi → P.1 ≤ a * N → P.2 ≤ b * N →
      ηlo < ((pointRank a b N P : ℤ) : ℚ) → ((pointRank a b N P : ℤ) : ℚ) < ηhi →
        (∀ Q : ℕ × ℕ, Q.1 ≤ a * N → Q.2 ≤ b * N →
            ηlo < ((pointRank a b N Q : ℤ) : ℚ) → ((pointRank a b N Q : ℤ) : ℚ) < ηhi →
            pointRank a b N Q = pointRank a b N P) →
          ∀ yB yE : Heights a b N, IsAboveDiagonal yB → IsAboveDiagonal yE →
            P ∈ sweptRegion yB → eventType yB P = EventType.B →
              eventType yE P = EventType.E → colouring yB ηlo = colouring yE ηlo →
                R ηlo (colouring yB ηlo)
                  = dminus q (sweepWidth yB P) (R ηhi (colouring yB ηhi))
                      + u • R ηhi (colouring yE ηhi)

/-- **The unswept clause of the level recursion above the floor `aN`**, verbatim
`HJO.Mellit.SweepRecursionUnswept` with `aN < ηlo` inserted. -/
def SweepRecursionUnsweptFloor (a b N : ℕ) (R : ℚ → Finset (ℕ × ℕ) → Total L) : Prop :=
  ∀ (X Y : ℕ) (ηlo ηhi : ℚ), ((a * N : ℕ) : ℚ) < ηlo → Isolates a b N X Y ηlo ηhi →
    ∀ y : Heights a b N, IsAboveDiagonal y → (X, Y) ∉ sweptRegion y →
      R ηlo (colouring y ηlo) = R ηhi (colouring y ηhi)

/-! ### The floored clauses are weakenings, and nothing else changed -/

/-- **The floored `A`/`C`/`D` clause is the unfloored one with one hypothesis added.** The proof
discards the floor and passes everything else through unchanged, so it typechecks only if the two
`Prop`s differ in exactly that hypothesis. -/
theorem sweepRecursionACDFloor_of_sweepRecursionACD {q u : L}
    {R : ℚ → Finset (ℕ × ℕ) → Total L} (h : SweepRecursionACD q u a b N R) :
    SweepRecursionACDFloor q u a b N R :=
  fun X Y ηlo ηhi _ => h X Y ηlo ηhi

/-- **The step-restricted clause is the floored one with one further hypothesis added.** Same
reading as `HJO.Mellit.sweepRecursionACDFloor_of_sweepRecursionACD`. -/
theorem sweepRecursionACDFloorStep_of_sweepRecursionACDFloor {q u : L}
    {R : ℚ → Finset (ℕ × ℕ) → Total L} (h : SweepRecursionACDFloor q u a b N R) :
    SweepRecursionACDFloorStep q u a b N R :=
  fun X Y ηlo ηhi hfl _ => h X Y ηlo ηhi hfl

/-- **The floored `BE` clause is the unfloored one with one hypothesis added.** -/
theorem sweepRecursionBEFloor_of_sweepRecursionBE {q u : L}
    {R : ℚ → Finset (ℕ × ℕ) → Total L} (h : SweepRecursionBE q u a b N R) :
    SweepRecursionBEFloor q u a b N R :=
  fun P ηlo ηhi _ => h P ηlo ηhi

omit [Algebra ℚ L] in
/-- **The floored unswept clause is the unfloored one with one hypothesis added.** -/
theorem sweepRecursionUnsweptFloor_of_sweepRecursionUnswept
    {R : ℚ → Finset (ℕ × ℕ) → Total L} (h : SweepRecursionUnswept a b N R) :
    SweepRecursionUnsweptFloor a b N R :=
  fun X Y ηlo ηhi _ => h X Y ηlo ηhi

/-! ### Above the floor the origin never arises -/

/-- **The floor excludes the origin.** The rank of `(0, 0)` is `0`, so a bracketing of the origin
puts the lower level below `0`, while the floor puts it above `aN ≥ 0`.

This is why the floored iteration needs no origin clause: `HJO.Mellit.SweepRecursionBOrigin` is the
clause that supplies the one point `HJO.Mellit.SweepRecursionACD` cannot reach and
`HJO.Mellit.SweepRecursionBE` is vacuous at, and above the floor that point is not bracketed at
all. -/
theorem ne_origin_of_floor {X Y : ℕ} {ηlo ηhi : ℚ} (hI : Isolates a b N X Y ηlo ηhi)
    (hfl : ((a * N : ℕ) : ℚ) < ηlo) : ((X, Y) : ℕ × ℕ) ≠ ((0 : ℕ), (0 : ℕ)) := by
  rintro h
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
  have h0 : ((pointRank a b N ((0 : ℕ), (0 : ℕ)) : ℤ) : ℚ) = 0 := by
    rw [cast_pointRank_eq]; ring
  have hlt := hI.ltP
  rw [h0] at hlt
  have hnn : (0 : ℚ) ≤ ((a * N : ℕ) : ℚ) := Nat.cast_nonneg _
  linarith

/-! ### One drop, above the floor -/

/-- **One drop of the level transfers agreement, above the floor, at every bracketed point.** The
counterpart of `HJO.Mellit.eq_dsc_of_recursion_step_any` with the floored clauses, and with the
origin clause absent: by `HJO.Mellit.ne_origin_of_floor` the bracketed point is not the origin, so
`HJO.Mellit.hasBEPartner_of_isolates` supplies the partner obligation and the `BE` clause can be
applied to whichever of the two paths is in hand. -/
theorem eq_dsc_of_recursion_step_any_floor (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {R : ℚ → Finset (ℕ × ℕ) → Total L} (hACD : SweepRecursionACDFloor q u a b N R)
    (hBE : SweepRecursionBEFloor q u a b N R) (hUn : SweepRecursionUnsweptFloor a b N R)
    {X Y : ℕ} {ηlo ηhi : ℚ} (hI : Isolates a b N X Y ηlo ηhi)
    (hfl : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hhi : ∀ z : Heights a b N, IsAboveDiagonal z →
      R ηhi (colouring z ηhi) = dsc q u a b N ηhi (colouring z ηhi)) :
    R ηlo (colouring y ηlo) = dsc q u a b N ηlo (colouring y ηlo) := by
  by_cases hsw : (X, Y) ∈ sweptRegion y
  · have hpart := hasBEPartner_of_isolates ha hb hN hI hy hsw (ne_origin_of_floor hI hfl)
    have hacd : ∀ _hAB : ht y X < Y ∨ ht y (X + 1) = Y,
        R ηlo (colouring y ηlo) = dsc q u a b N ηlo (colouring y ηlo) := fun hAB => by
      rw [hACD X Y ηlo ηhi hfl hI y hy hsw hAB, hhi y hy,
        dsc_lo_eq_sweepOperator_dsc_hi q u ha hb hN hI hy hsw hAB]
    cases hev : eventType y (X, Y) with
    | A => exact hacd (ht_lt_or_ht_succ_eq_of_eventType ha hsw (Or.inl hev))
    | C => exact hacd (ht_lt_or_ht_succ_eq_of_eventType ha hsw (Or.inr (Or.inl hev)))
    | D => exact hacd (ht_lt_or_ht_succ_eq_of_eventType ha hsw (Or.inr (Or.inr hev)))
    | B =>
      obtain ⟨z, hz, hcol, hzev⟩ := hpart.1 hev
      rw [hBE (X, Y) ηlo ηhi hfl hI.lo hI.hi hI.xle hI.yle hI.ltP hI.Plt hI.iso y z hy hz hsw hev
          hzev hcol, hhi y hy, hhi z hz,
        dsc_eq_dminus_add_smul q u ha hb hN hI.lo hI.hi hI.xle hI.yle hI.ltP hI.Plt hI.iso hy hz
          hsw hev hzev hcol]
    | E =>
      obtain ⟨z, hz, hcol, hzsw, hzev⟩ := hpart.2 hev
      rw [← hcol, hBE (X, Y) ηlo ηhi hfl hI.lo hI.hi hI.xle hI.yle hI.ltP hI.Plt hI.iso z y hz hy
          hzsw hzev hev hcol, hhi y hy, hhi z hz,
        dsc_eq_dminus_add_smul q u ha hb hN hI.lo hI.hi hI.xle hI.yle hI.ltP hI.Plt hI.iso hz hy
          hzsw hzev hev hcol]
  · rw [hUn X Y ηlo ηhi hfl hI y hy hsw, hhi y hy,
      dsc_lo_eq_dsc_hi_of_notMem_sweptRegion q u ha hb hN hI hy hsw]

/-! ### The iteration above the floor -/

/-- **The iteration principle above the floor.** A candidate satisfying the three floored recursion
clauses and the initial condition agrees with `HJO.Mellit.dsc` at every admissible level above
`aN`.

The proof is the induction of `HJO.Mellit.agreesWithDsc_of_recursions` with the floor threaded
through, and the threading is the content: the upper level of the drop is `rk̂(X, Y) + 1/2` with
`ηlo < rk̂(X, Y)`, so it is above `ηlo` and hence above the floor. The chain therefore never leaves
the floored region, and the base case — no rank of the rectangle above the level — sits at the top
of it.

Four hypotheses, not five: `HJO.Mellit.SweepRecursionBOrigin` is not needed, by
`HJO.Mellit.ne_origin_of_floor`. -/
theorem agreesWithDsc_of_recursions_floor (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {R : ℚ → Finset (ℕ × ℕ) → Total L} (hACD : SweepRecursionACDFloor q u a b N R)
    (hBE : SweepRecursionBEFloor q u a b N R) (hUn : SweepRecursionUnsweptFloor a b N R)
    (hinit : SweepInitialCondition a b N R) {η : ℚ} (hη : IsAdmissibleLevel η)
    (hfl : ((a * N : ℕ) : ℚ) < η) : AgreesWithDsc q u a b N R η := by
  suffices H : ∀ n : ℕ, ∀ η : ℚ, IsAdmissibleLevel η → ((a * N : ℕ) : ℚ) < η →
      #(ranksAbove a b N η) ≤ n → AgreesWithDsc q u a b N R η from H _ η hη hfl le_rfl
  intro n
  induction n with
  | zero =>
    intro η hη _ hcard
    exact agreesWithDsc_of_ranksAbove_eq_empty q u ha hinit hη
      (Finset.card_eq_zero.1 (Nat.le_zero.1 hcard))
  | succ n ih =>
    intro η hη hfl hcard
    by_cases hempty : ranksAbove a b N η = ∅
    · exact agreesWithDsc_of_ranksAbove_eq_empty q u ha hinit hη hempty
    obtain ⟨P, hP, hmin⟩ := Finset.exists_min_image (ranksAbove a b N η) (pointRank a b N)
      (Finset.nonempty_iff_ne_empty.2 hempty)
    obtain ⟨X, Y⟩ := P
    obtain ⟨hX, hY, hPη⟩ := mem_ranksAbove.1 hP
    have hIhi : IsAdmissibleLevel (((pointRank a b N (X, Y) : ℤ) : ℚ) + 1 / 2) :=
      ⟨pointRank a b N (X, Y), rfl⟩
    have hI : Isolates a b N X Y η (((pointRank a b N (X, Y) : ℤ) : ℚ) + 1 / 2) := by
      refine ⟨hη, hIhi, hPη, by norm_num, ?_, hX, hY⟩
      intro Q hQ1 hQ2 hlo hhi
      have h1 : pointRank a b N (X, Y) ≤ pointRank a b N Q :=
        hmin Q (mem_ranksAbove.2 ⟨hQ1, hQ2, hlo⟩)
      have h2 : pointRank a b N Q ≤ pointRank a b N (X, Y) := by
        by_contra hcon
        have h3 : ((pointRank a b N (X, Y) : ℤ) : ℚ) + 1 ≤
            ((pointRank a b N Q : ℤ) : ℚ) := by
          have h4 : pointRank a b N (X, Y) + 1 ≤ pointRank a b N Q := by omega
          exact_mod_cast h4
        linarith
      omega
    have hsub : ranksAbove a b N (((pointRank a b N (X, Y) : ℤ) : ℚ) + 1 / 2) ⊆
        ranksAbove a b N η := by
      intro Q hQ
      obtain ⟨h1, h2, h3⟩ := mem_ranksAbove.1 hQ
      exact mem_ranksAbove.2 ⟨h1, h2, hPη.trans (by linarith)⟩
    have hnot : ((X, Y) : ℕ × ℕ) ∉
        ranksAbove a b N (((pointRank a b N (X, Y) : ℤ) : ℚ) + 1 / 2) :=
      fun hcon => absurd (mem_ranksAbove.1 hcon).2.2 (by norm_num)
    have hcard' : #(ranksAbove a b N (((pointRank a b N (X, Y) : ℤ) : ℚ) + 1 / 2)) ≤ n := by
      have hlt := Finset.card_lt_card (LE.le.ssubset_of_mem_notMem hsub hP hnot)
      omega
    have hflhi : ((a * N : ℕ) : ℚ) < ((pointRank a b N (X, Y) : ℤ) : ℚ) + 1 / 2 := by linarith
    intro y hy
    exact eq_dsc_of_recursion_step_any_floor q u ha hb hN hACD hBE hUn hI hfl hy
      (ih _ hIhi hflhi hcard')

/-- **The iteration principle above the floor, at an admissible colouring**, which is the shape
Mellit's Theorem 5.8 is stated in. `HJO.Mellit.eq_dsc_of_recursions` with the floor. -/
theorem eq_dsc_of_recursions_floor (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {R : ℚ → Finset (ℕ × ℕ) → Total L} (hACD : SweepRecursionACDFloor q u a b N R)
    (hBE : SweepRecursionBEFloor q u a b N R) (hUn : SweepRecursionUnsweptFloor a b N R)
    (hinit : SweepInitialCondition a b N R) {η : ℚ} (hη : IsAdmissibleLevel η)
    (hfl : ((a * N : ℕ) : ℚ) < η) {c : Finset (ℕ × ℕ)}
    (hc : IsAdmissibleColouring a b N η c) : R η c = dsc q u a b N η c := by
  obtain ⟨y, hy, rfl⟩ := hc
  exact agreesWithDsc_of_recursions_floor q u ha hb hN hACD hBE hUn hinit hη hfl y hy

/-- **The floored iteration still reaches the separating levels.** `HJO.Mellit.sepLevel a N` is
`aN + 1/2`, which is above the floor `aN` by half a unit — so the level at which
`HJO.Mellit.braidValueColouring_eq_dsc_floor` reads the invariant is inside the floored region,
and the floor costs nothing there. -/
theorem eq_dsc_sepLevel_floor (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {R : ℚ → Finset (ℕ × ℕ) → Total L} (hACD : SweepRecursionACDFloor q u a b N R)
    (hBE : SweepRecursionBEFloor q u a b N R) (hUn : SweepRecursionUnsweptFloor a b N R)
    (hinit : SweepInitialCondition a b N R) {c : Finset (ℕ × ℕ)}
    (hc : IsAdmissibleColouring a b N (sepLevel a N) c) :
    R (sepLevel a N) c = dsc q u a b N (sepLevel a N) c :=
  eq_dsc_of_recursions_floor q u ha hb hN hACD hBE hUn hinit (isAdmissibleLevel_sepLevel a N)
    (by rw [sepLevel]; push_cast; linarith) hc

/-! ### Every level used downstream is above the floor -/

/-- **An admissible separating level is above the floor.** `HJO.Mellit.SeparatesDiagonal` tests the
corner `(aN, bN)`, which lies *on* the diagonal — `b·aN = a·bN` — and whose above-diagonal rank is
`aN`. So the separating property forces `aN ≤ η`, and admissibility upgrades that to `aN < η`, an
integer never being a half-integer.

This is the answer to the question the floor raises. `HJO.Mellit.MellitInduction`, the `hind` binder
of `HJO.Mellit.shuffle_of_lhs_and_induction`, quantifies over the admissible levels that separate
the diagonal, and **every one of them is inside the floored region**. The floor therefore costs
nothing at the point of use: it is not an extra hypothesis a user of the result must supply, it
is a consequence of the hypothesis the user already has. -/
theorem lt_of_separatesDiagonal {η : ℚ} (hη : IsAdmissibleLevel η)
    (hsep : SeparatesDiagonal a b N η) : ((a * N : ℕ) : ℚ) < η := by
  have hdiag : (b : ℤ) * (a * N) ≤ (a : ℤ) * (b * N) := le_of_eq (by ring)
  have hiff := hsep (a * N) (b * N) le_rfl le_rfl hdiag
  have hrank : ((abovePointRank a b N (a * N) (b * N) : ℤ) : ℚ) = ((a * N : ℕ) : ℚ) := by
    simp only [abovePointRank]
    push_cast
    ring
  have hle : ((a * N : ℕ) : ℚ) ≤ η := by
    by_contra hcon
    exact absurd (hiff.1 (by rw [hrank]; exact lt_of_not_ge hcon))
      (by rw [not_lt]; exact le_of_eq (by push_cast; ring))
  obtain ⟨m, rfl⟩ := hη
  have hint : ((a * N : ℕ) : ℤ) ≤ m := by
    by_contra hcon
    have h1 : (m : ℚ) + 1 ≤ ((a * N : ℕ) : ℚ) := by
      have h2 : m + 1 ≤ ((a * N : ℕ) : ℤ) := by omega
      exact_mod_cast h2
    linarith
  have h3 : ((a * N : ℕ) : ℚ) ≤ (m : ℚ) := by exact_mod_cast hint
  linarith

/-- **The floored iteration settles every admissible separating level.** By
`HJO.Mellit.lt_of_separatesDiagonal` the separating property implies the floor, so the three floored
clauses and the initial condition are enough at every level `HJO.Mellit.MellitInduction` asks about
— the `hind` binder of `HJO.Mellit.shuffle_of_lhs_and_induction` included.

`HJO.Mellit.eq_dsc_sepLevel_floor` is the special case `η = HJO.Mellit.sepLevel a N`; this is the
statement that nothing was special about that level. -/
theorem eq_dsc_of_recursions_separatesDiagonal (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {R : ℚ → Finset (ℕ × ℕ) → Total L} (hACD : SweepRecursionACDFloor q u a b N R)
    (hBE : SweepRecursionBEFloor q u a b N R) (hUn : SweepRecursionUnsweptFloor a b N R)
    (hinit : SweepInitialCondition a b N R) {η : ℚ} (hη : IsAdmissibleLevel η)
    (hsep : SeparatesDiagonal a b N η) {c : Finset (ℕ × ℕ)}
    (hc : IsAdmissibleColouring a b N η c) : R η c = dsc q u a b N η c :=
  eq_dsc_of_recursions_floor q u ha hb hN hACD hBE hUn hinit hη
    (lt_of_separatesDiagonal hη hsep) hc

/-! ### The left-hand side satisfies the floored clauses too -/

/-- **`HJO.Mellit.dsc` satisfies the three floored clauses and the initial condition**, immediately
from `HJO.Mellit.dsc_recursions` and the three weakenings. The floored principle is therefore not a
statement about an empty class of candidates, and — read the other way — the floor is not a
restriction `HJO.Mellit.dsc` fails to meet. -/
theorem dsc_recursions_floor (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    SweepRecursionACDFloor q u a b N (dsc q u a b N) ∧
      SweepRecursionBEFloor q u a b N (dsc q u a b N) ∧
      SweepRecursionUnsweptFloor a b N (dsc q u a b N) ∧
      SweepInitialCondition a b N (dsc q u a b N) :=
  ⟨sweepRecursionACDFloor_of_sweepRecursionACD (dsc_sweepRecursionACD q u ha hb hN),
    sweepRecursionBEFloor_of_sweepRecursionBE (dsc_sweepRecursionBE q u ha hb hN),
    sweepRecursionUnsweptFloor_of_sweepRecursionUnswept (dsc_sweepRecursionUnswept q u ha hb hN),
    dsc_sweepInitialCondition q u ha⟩

/-- **`HJO.Mellit.dsc` satisfies the step-restricted clause as well**, so the restriction of
`HJO.Mellit.SweepRecursionACDFloorStep` is not one the left-hand side fails either. Recorded so
that the difference between that clause and `HJO.Mellit.SweepRecursionACDFloor` cannot be read as a
defect of one of the two candidates: it is a difference in the range of level pairs quantified
over, and both candidates meet the narrower one. -/
theorem dsc_sweepRecursionACDFloorStep (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    SweepRecursionACDFloorStep q u a b N (dsc q u a b N) :=
  sweepRecursionACDFloorStep_of_sweepRecursionACDFloor
    (sweepRecursionACDFloor_of_sweepRecursionACD (dsc_sweepRecursionACD q u ha hb hN))

/-! ### The worked instance, re-derived above the floor -/

/-- **The floored principle still pins the candidate down at a two-element colouring in range.**
`HJO.Mellit.eq_dsc_of_recursions_example` is the check that the unfloored principle is not a
statement about the empty colouring alone: on the `2 × 3` rectangle the level `7/2` is admissible
and `{(0,0), (1,3)}` is the colouring there of the above-diagonal path `(0, 2, 3)`. The floor at
those parameters is `aN = 2 < 7/2`, so that instance is inside the floored region and the floored
principle reproves it — with **three** clauses instead of four, the origin clause unused.

`HJO.Mellit.eq_dsc_of_recursions_example_eq_floor` checks by `rfl` that the statement reproved is
the very one `HJO.Mellit.eq_dsc_of_recursions_example` states. -/
theorem eq_dsc_of_recursions_example_floor (q u : L) {R : ℚ → Finset (ℕ × ℕ) → Total L}
    (hACD : SweepRecursionACDFloor q u 2 3 1 R) (hBE : SweepRecursionBEFloor q u 2 3 1 R)
    (hUn : SweepRecursionUnsweptFloor 2 3 1 R) (hinit : SweepInitialCondition 2 3 1 R) :
    R (7 / 2) {(0, 0), (1, 3)} = dsc q u 2 3 1 (7 / 2) {(0, 0), (1, 3)} :=
  eq_dsc_of_recursions_floor q u (by norm_num) (by norm_num) (by norm_num) hACD hBE hUn hinit
    ⟨3, by norm_num⟩ (by norm_num)
    ⟨(![0, 2, 3] : Heights 2 3 1), by decide, colouring_thm42_be_witness.1⟩

/-- **The floored route reproves the unfloored worked instance, and not a weaker statement.**
`Prop` is proof-irrelevant, so this `rfl` typechecks exactly when the two theorems have the same
conclusion — which is the check that
`HJO.Mellit.eq_dsc_of_recursions_example_floor` is the same claim as
`HJO.Mellit.eq_dsc_of_recursions_example`, reached without the origin clause and without the
unfloored clauses. -/
theorem eq_dsc_of_recursions_example_eq_floor (q u : L) {R : ℚ → Finset (ℕ × ℕ) → Total L}
    (hACD : SweepRecursionACD q u 2 3 1 R) (hBE : SweepRecursionBE q u 2 3 1 R)
    (hB0 : SweepRecursionBOrigin q 2 3 1 R) (hUn : SweepRecursionUnswept 2 3 1 R)
    (hinit : SweepInitialCondition 2 3 1 R) :
    eq_dsc_of_recursions_example q u hACD hBE hB0 hUn hinit
      = eq_dsc_of_recursions_example_floor q u
          (sweepRecursionACDFloor_of_sweepRecursionACD hACD)
          (sweepRecursionBEFloor_of_sweepRecursionBE hBE)
          (sweepRecursionUnsweptFloor_of_sweepRecursionUnswept hUn) hinit :=
  rfl

end HJO.Mellit

end
