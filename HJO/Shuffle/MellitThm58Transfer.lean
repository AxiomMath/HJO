/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitThm42
public import HJO.Shuffle.MellitThm42BE

/-! # Mellit's closing sentence, as a theorem: one step of the colouring recursion transfers

Mellit's Theorem 5.8 (`HJO.Mellit.braidValueColouring_eq_dsc_floor`) is proved in A. Mellit,
*Toric braids and `(m, n)`-parking functions*, arXiv:1604.07456, §5, by one sentence:

> Now we see that both sides of the statement satisfy the same recursions and the same initial
> conditions, so the proof is complete.

The recursion is his Theorem 4.2, whose four rules `A`, `C`, `D`, `BE` are all
proved in Lean for the left-hand side `D_{η,c}` — `HJO.Mellit.dsc_lo_eq_sweepOperator_dsc_hi`
carries `A`, `C` and `D` together and `HJO.Mellit.dsc_eq_dminus_add_smul` carries `BE`. This file
asks what that sentence actually needs, by abstracting the *right*-hand side to an arbitrary
candidate `R` and proving the transfer step: if `R` satisfies the same two recursion clauses and
agrees with `dsc` at the upper level, does it agree at the lower level?

## The verdict, and the obligation the sentence hides

It does — **but only at the three event types `A`, `C`, `D`. At the types `B` and `E` the two
clauses do not determine the value, and the missing input is an existence statement that
Mellit asserts in one clause and never proves.**

`HJO.Mellit.eq_dsc_of_recursion_step` is the transfer, and its hypothesis list is the finding: past
the recursion clauses and the agreement at the upper level it needs
`HJO.Mellit.HasBEPartner`, which says that a path whose event at `P` has type `B` is accompanied by
an above-diagonal path with the same colouring below the level whose event at `P` has type `E`, and
conversely. That is the Lean content of Mellit's sentence just before Theorem 4.2,

> If `P` is inside `c`, then `c` can be obtained in `2` ways: from `c' ∈ 𝒞_{h_+}` by rule B) or from
> `c'' ∈ 𝒞_{h_+}` by rule E).

The reason it is an obligation rather than a remark is the *shape* of rule `BE`. Rules `A`, `C` and
`D` have one predecessor and read it off the same path, so one path suffices to apply them. Rule
`BE` has two, carried by two *different* paths `P̂` and `Q̂`, and
`HJO.Mellit.dsc_eq_dminus_add_smul` takes both as hypotheses — correctly, since it is an identity
about whichever two paths are supplied. So at a type-`B` event the rule says nothing at all until a
type-`E` partner is produced, and a recursion that says nothing does not determine a value. None
of this is visible in the statement of rule `BE` itself, because the missing statement is not a
lemma that rule depends on: it is a hypothesis the rule carries.

`HJO.Mellit.eq_dsc_of_recursion_step_acd` is the same transfer at the types `A`, `C` and `D` alone,
where the partner hypothesis is not needed and nothing is owed.

Two things keep this finding from overstating itself. The obligation is *satisfiable*, and exhibited
in range: `HJO.Mellit.hasBEPartner_two_three_one_B` and `HJO.Mellit.hasBEPartner_two_three_one_E`
produce the partner on the `2 × 3` rectangle, and in general it holds at every bracketed swept point
other than the origin (`HJO.Mellit.hasBEPartner_of_isolates`, in
`HJO/Shuffle/MellitBEPartner.lean`). And it is *unavoidable*: `HJO.Mellit.beClause_unavoidable`
shows that the origin is a type-`B` event for every above-diagonal path, which is Mellit's own
parenthesis "in the very end, when we cross the point `(0,0)` we have to apply B)". So the one
clause with two predecessors fires at every sweep, at the last point, and cannot be routed around;
there the partner does not exist (`HJO.Mellit.not_hasBEPartner_origin`), and the drop is instead
made by rule `B` alone (`HJO/Shuffle/MellitOriginTransfer.lean`).

## What this does and does not settle

It settles the *logical* shape of Mellit's sentence at one level drop, and no more. Three things it
does not do, each worth stating so the theorem is not read for more than it says.

*It does not supply the braid half.* `R` is abstract on purpose, and the braid side of
`HJO.Mellit.braidValueColouring_eq_dsc_floor` — `q^{(inv_fin - inv_ini)/2} π_k(B_{s,c}) d_+^k(1)` —
is a perfectly writable instance of it: `π_k` is `HJO.Sweep.Mellit.braidRepMellit`, which carries no
open hypothesis, only the genericity `q ≠ 0`, `q ≠ 1`, `q + 1 ≠ 0` and a square root `r * r = q`,
its well-definedness being `HJO.Sweep.Mellit.braidRepRespects_mellit`. That this instance
satisfies the recursion clauses, in floored form above the level `aN`, is a separate theorem,
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor`, and nothing here bears on it.

*It does not iterate.* Chaining the drops from a level above the whole rectangle down to a
separating level is a second, separate step (`HJO/Shuffle/MellitThm58Iteration.lean`), and it is not
a matter of repeating this one:
the colouring of `HJO.Mellit.colouring` moves both when the level passes a rank and when it passes a
rank *plus* the attack window — that is what the hypothesis of
`HJO.Mellit.isAdmissibleColouring_empty_and_dsc_eq_one` is about — while the four rules are keyed to
the ranks alone.

*And Mellit's level recursion is not the only route to `HJO.Mellit.braidValueColouring_eq_dsc_floor`
in this library.* The braid side already satisfies a *different* recursion, over the parts of a
composition rather than over level drops: `HJO.Mellit.braidRep_specialBraid_dplusIter`, proved with
every hypothesis discharged as `HJO.Mellit.sweepIn_braidRep_specialBraid_appendFinalTuple`. That is
the recursion `HJO.Mellit.IsBraidValue` abstracts, and by
`HJO.Mellit.mellitInduction_iff_braidClosedForm` what is then missing is
`HJO.Mellit.IsColouringValue` for it — which is `HJO.Mellit.braidValueColouring_eq_dsc_floor` at the
composition colourings alone. So the obligation this file isolates is the one on *Mellit's* route,
and the library carries a second route whose braid half is already proved.

No genericity is spent. Both recursion clauses are carried as hypotheses on `R` in exactly the shape
the `dsc` rules state them, so every inverse in `HJO.Sweep.corner` (`q - 1`) and in
`HJO.Sweep.zop` (`q u`) sits inside those hypotheses rather than in anything proved here; the
theorems below hold at every `q` and `u` in a field, because they assume the identities rather than
evaluating them.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {a b N : ℕ}

/-! ### The two clauses of the recursion, as properties of a candidate -/

/-- **The `A`/`C`/`D` clause of Mellit's Theorem 4.2, asked of a candidate `R`.** Verbatim the shape
of `HJO.Mellit.dsc_lo_eq_sweepOperator_dsc_hi`, which is this statement for `R = dsc`: at a
bracketed lattice point `(X, Y)` swept by an above-diagonal path `y` whose event there is not of
type `B` or `E` — that is what `ht y X < Y ∨ ht y (X + 1) = Y` says, by
`HJO.Mellit.ht_lt_or_ht_succ_eq_of_eventType` — lowering the level multiplies the invariant by the
event's own operator `HJO.Sweep.sweepOperator`. -/
def SweepRecursionACD (q u : L) (a b N : ℕ) (R : ℚ → Finset (ℕ × ℕ) → Total L) : Prop :=
  ∀ (X Y : ℕ) (ηlo ηhi : ℚ), Isolates a b N X Y ηlo ηhi →
    ∀ y : Heights a b N, IsAboveDiagonal y → (X, Y) ∈ sweptRegion y →
      (ht y X < Y ∨ ht y (X + 1) = Y) →
        R ηlo (colouring y ηlo) = sweepOperator q u y (X, Y) (R ηhi (colouring y ηhi))

/-- **The `BE` clause of Mellit's Theorem 4.2, asked of a candidate `R`.** Verbatim the shape of
`HJO.Mellit.dsc_eq_dminus_add_smul`, including its two paths: the clause is an identity relating the
value below the level to the values above it at *both* upper colourings, the type-`B` one carrying
`d_-` and the type-`E` one carrying `u`. -/
def SweepRecursionBE (q u : L) (a b N : ℕ) (R : ℚ → Finset (ℕ × ℕ) → Total L) : Prop :=
  ∀ (P : ℕ × ℕ) (ηlo ηhi : ℚ), IsAdmissibleLevel ηlo → IsAdmissibleLevel ηhi →
    P.1 ≤ a * N → P.2 ≤ b * N →
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

/-- **The existence statement rule `BE` needs and Mellit asserts in passing.** At a lattice
point `P` and a lower level `ηlo`, an above-diagonal path `y` *has a `BE` partner* when the event
type at `P` that `y` does not realise is realised by some above-diagonal path with the same
colouring at `ηlo`.

This is what makes rule `BE` usable as a recursion. The rule is an identity about two supplied
paths; to *compute* with it at a path whose event is of type `B` one must produce the type-`E` path,
and at a path of type `E` the type-`B` path. Mellit's "`c` can be obtained in `2` ways" is exactly
the assertion that both always exist, which he does not prove. Here it is
`HJO.Mellit.hasBEPartner_of_isolates`, at every bracketed swept point other than the origin, where
it fails (`HJO.Mellit.not_hasBEPartner_origin`). -/
def HasBEPartner (a b N : ℕ) (ηlo : ℚ) (P : ℕ × ℕ) (y : Heights a b N) : Prop :=
  (eventType y P = EventType.B →
      ∃ z : Heights a b N, IsAboveDiagonal z ∧ colouring y ηlo = colouring z ηlo ∧
        eventType z P = EventType.E) ∧
    (eventType y P = EventType.E →
      ∃ z : Heights a b N, IsAboveDiagonal z ∧ colouring z ηlo = colouring y ηlo ∧
        P ∈ sweptRegion z ∧ eventType z P = EventType.B)

/-! ### The transfer -/

/-- **One drop of the level transfers agreement, at the event types `A`, `C` and `D`.** If a
candidate `R` satisfies the `A`/`C`/`D` clause of Mellit's Theorem 4.2 and agrees with
`HJO.Mellit.dsc` at the upper level on the colouring of the path in question, then it agrees at the
lower level. Nothing is owed here: the clause has one predecessor and reads it off the same path.

The event hypothesis is stated as the disjunction `HJO.Mellit.dsc_lo_eq_sweepOperator_dsc_hi` takes,
so no case analysis is needed; `HJO.Mellit.ht_lt_or_ht_succ_eq_of_eventType` produces it from
`eventType y (X, Y) ∈ {A, C, D}`. -/
theorem eq_dsc_of_recursion_step_acd (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {R : ℚ → Finset (ℕ × ℕ) → Total L} (hR : SweepRecursionACD q u a b N R) {X Y : ℕ}
    {ηlo ηhi : ℚ} (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hPsw : (X, Y) ∈ sweptRegion y) (hAB : ht y X < Y ∨ ht y (X + 1) = Y)
    (hhi : R ηhi (colouring y ηhi) = dsc q u a b N ηhi (colouring y ηhi)) :
    R ηlo (colouring y ηlo) = dsc q u a b N ηlo (colouring y ηlo) := by
  rw [hR X Y ηlo ηhi hI y hy hPsw hAB, hhi,
    dsc_lo_eq_sweepOperator_dsc_hi q u ha hb hN hI hy hPsw hAB]

/-- **One drop of the level transfers agreement, at every event type — given the `BE` partner.**
Mellit's closing sentence at one lattice point, with the right-hand side abstracted: a candidate `R`
satisfying both clauses of Theorem 4.2 and agreeing with `HJO.Mellit.dsc` at the upper level on
*every* above-diagonal path's colouring agrees with it at the lower level.

The hypothesis `HJO.Mellit.HasBEPartner` is the whole point of the statement. At the types `A`, `C`
and `D` it is not used — `HJO.Mellit.eq_dsc_of_recursion_step_acd` is that part — and at the types
`B` and `E` nothing can be concluded without it, because rule `BE` relates the lower value to the
upper values of two different paths and supplies neither. So this theorem is the precise sense in
which "both sides satisfy the same recursions" closes Theorem 5.8: it closes it modulo the existence
statement `HJO.Mellit.HasBEPartner`. -/
theorem eq_dsc_of_recursion_step (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {R : ℚ → Finset (ℕ × ℕ) → Total L} (hACD : SweepRecursionACD q u a b N R)
    (hBE : SweepRecursionBE q u a b N R) {X Y : ℕ} {ηlo ηhi : ℚ}
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hPsw : (X, Y) ∈ sweptRegion y) (hpart : HasBEPartner a b N ηlo (X, Y) y)
    (hhi : ∀ z : Heights a b N, IsAboveDiagonal z →
      R ηhi (colouring z ηhi) = dsc q u a b N ηhi (colouring z ηhi)) :
    R ηlo (colouring y ηlo) = dsc q u a b N ηlo (colouring y ηlo) := by
  cases hev : eventType y (X, Y) with
  | A =>
    exact eq_dsc_of_recursion_step_acd q u ha hb hN hACD hI hy hPsw
      (ht_lt_or_ht_succ_eq_of_eventType ha hPsw (Or.inl hev)) (hhi y hy)
  | C =>
    exact eq_dsc_of_recursion_step_acd q u ha hb hN hACD hI hy hPsw
      (ht_lt_or_ht_succ_eq_of_eventType ha hPsw (Or.inr (Or.inl hev))) (hhi y hy)
  | D =>
    exact eq_dsc_of_recursion_step_acd q u ha hb hN hACD hI hy hPsw
      (ht_lt_or_ht_succ_eq_of_eventType ha hPsw (Or.inr (Or.inr hev))) (hhi y hy)
  | B =>
    obtain ⟨z, hz, hcol, hzev⟩ := hpart.1 hev
    rw [hBE (X, Y) ηlo ηhi hI.lo hI.hi hI.xle hI.yle hI.ltP hI.Plt hI.iso y z hy hz hPsw hev
        hzev hcol, hhi y hy, hhi z hz,
      dsc_eq_dminus_add_smul q u ha hb hN hI.lo hI.hi hI.xle hI.yle hI.ltP hI.Plt hI.iso hy hz
        hPsw hev hzev hcol]
  | E =>
    obtain ⟨z, hz, hcol, hzsw, hzev⟩ := hpart.2 hev
    rw [← hcol, hBE (X, Y) ηlo ηhi hI.lo hI.hi hI.xle hI.yle hI.ltP hI.Plt hI.iso z y hz hy hzsw
        hzev hev hcol, hhi y hy, hhi z hz,
      dsc_eq_dminus_add_smul q u ha hb hN hI.lo hI.hi hI.xle hI.yle hI.ltP hI.Plt hI.iso hz hy
        hzsw hzev hev hcol]

/-! ### The left-hand side satisfies its own recursion -/

/-- **`HJO.Mellit.dsc` satisfies the `A`/`C`/`D` clause**, which is
`HJO.Mellit.dsc_lo_eq_sweepOperator_dsc_hi` packaged as
`HJO.Mellit.SweepRecursionACD`. Recorded so that the abstraction above is known to be inhabited: a
recursion property with no example is a hypothesis nothing satisfies, and the transfer theorems
would then be vacuous in the same way the Mellit layer's `∀ Ω` clauses are. -/
theorem dsc_sweepRecursionACD (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    SweepRecursionACD q u a b N (dsc q u a b N) :=
  fun _ _ _ _ hI _ hy hPsw hAB => dsc_lo_eq_sweepOperator_dsc_hi q u ha hb hN hI hy hPsw hAB

/-- **`HJO.Mellit.dsc` satisfies the `BE` clause**, which is
`HJO.Mellit.dsc_eq_dminus_add_smul` packaged as `HJO.Mellit.SweepRecursionBE`. With
`HJO.Mellit.dsc_sweepRecursionACD` this shows both abstractions are inhabited, so
`HJO.Mellit.eq_dsc_of_recursion_step` is not a statement about an empty class of candidates. -/
theorem dsc_sweepRecursionBE (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    SweepRecursionBE q u a b N (dsc q u a b N) :=
  fun _ _ _ hlo hhi hP1 hP2 hrlo hrhi hiso _ _ hyB hyE hPB hevB hevE hcol =>
    dsc_eq_dminus_add_smul q u ha hb hN hlo hhi hP1 hP2 hrlo hrhi hiso hyB hyE hPB hevB hevE hcol

/-! ### The transfer is not vacuous, and the `BE` clause is not avoidable -/

/-- **Every lattice point of the rectangle is bracketed**, so `HJO.Mellit.Isolates` is inhabited and
the transfer theorems are not statements about an empty situation. This is
`HJO.Mellit.exists_isolating_isAdmissibleLevel`, whose
witnesses are `rk̂(P) ± 1/2` — with the two rectangle bounds folded in to build the structure. -/
theorem exists_isolates (a b N X Y : ℕ) (hx : X ≤ a * N) (hy : Y ≤ b * N) :
    ∃ ηlo ηhi : ℚ, Isolates a b N X Y ηlo ηhi := by
  obtain ⟨ηlo, ηhi, h1, h2, h3, h4, h5⟩ :=
    exists_isolating_isAdmissibleLevel a b N (P := (X, Y)) hx hy
  exact ⟨ηlo, ηhi, ⟨h1, h2, h3, h4, h5, hx, hy⟩⟩

/-- **The origin is in the swept region of every above-diagonal path.** Its three conditions are
`0 ≤ aN`, `b · 0 ≤ a · 0` and `0 ≤ ŷ_1`, and none of them asks anything of the path. -/
theorem mem_sweptRegion_origin {y : Heights a b N} : ((0 : ℕ), (0 : ℕ)) ∈ sweptRegion y :=
  mem_sweptRegion.2 ⟨Nat.zero_le _, by simp, Nat.zero_le _⟩

/-- **At the origin the event of every above-diagonal path is of type `B`.** The path starts at
height `0`, so the origin is its own foot; and `ŷ_1 > 0` because the above-diagonal condition gives
`b · 1 ≤ a · ŷ_1` with `b > 0`. Those are exactly the three clauses of
`HJO.Paths.eventType_eq_B_iff`.

This is Mellit's parenthesis in the statement of his sweep algorithm — "Note that in the very end,
when we cross the point `(0, 0)` we have to apply B)" — and it is why the `BE` clause of the
recursion cannot be routed around. See `HJO.Mellit.beClause_unavoidable`. -/
theorem eventType_origin_eq_B (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {y : Heights a b N}
    (hy : IsAboveDiagonal y) : eventType y ((0 : ℕ), (0 : ℕ)) = EventType.B := by
  have haN : 0 < a * N := Nat.mul_pos ha hN
  have hd : b * 1 ≤ a * ht y 1 := hy.2.2.2 1 haN
  refine eventType_eq_B_iff.2 ⟨hy.1.symm, haN, ?_⟩
  rcases Nat.eq_zero_or_pos (ht y 1) with h | h
  · rw [h, Nat.mul_zero] at hd; omega
  · exact h

/-- **The `BE` clause of the recursion fires at every sweep, so the partner obligation cannot be
avoided.** At the origin, for every above-diagonal path: the point is bracketed by admissible
levels, it lies in the swept region, and the event is of type `B` — hence *not* of type `A`, `C` or
`D`, so
`HJO.Mellit.eq_dsc_of_recursion_step_acd` does not apply there and
`HJO.Mellit.eq_dsc_of_recursion_step` must use `HJO.Mellit.HasBEPartner`.

This is why the existence statement matters to the whole argument and not only to one case.
A recursion that determined the value at every point except the last would still not determine it,
and the last point is precisely where the only clause with two predecessors is forced. -/
theorem beClause_unavoidable (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {y : Heights a b N}
    (hy : IsAboveDiagonal y) :
    (∃ ηlo ηhi : ℚ, Isolates a b N 0 0 ηlo ηhi) ∧ ((0 : ℕ), (0 : ℕ)) ∈ sweptRegion y ∧
      eventType y ((0 : ℕ), (0 : ℕ)) = EventType.B ∧
      eventType y ((0 : ℕ), (0 : ℕ)) ≠ EventType.A ∧
      eventType y ((0 : ℕ), (0 : ℕ)) ≠ EventType.C ∧
      eventType y ((0 : ℕ), (0 : ℕ)) ≠ EventType.D :=
  ⟨exists_isolates a b N 0 0 (Nat.zero_le _) (Nat.zero_le _), mem_sweptRegion_origin,
    eventType_origin_eq_B ha hb hN hy, by simp [eventType_origin_eq_B ha hb hN hy],
    by simp [eventType_origin_eq_B ha hb hN hy], by simp [eventType_origin_eq_B ha hb hN hy]⟩

/-! ### The obligation is satisfiable, and exhibited -/

/-- **`HJO.Mellit.HasBEPartner` holds at an explicit in-range instance, in both directions.** On the
`2 × 3` rectangle at the level `7/2` and the lattice point `(1, 2)`, the paths `(0,2,3)` and
`(0,3,3)` are each other's `BE` partner: they have the same colouring `{(0,0), (1,3)}` below the
level (`HJO.Mellit.colouring_thm42_be_witness`), the first has a type-`B` event at `(1, 2)` and
sweeps it, and the second has a type-`E` event there.

So the partner obligation is neither false nor unsatisfiable:
`HJO.Mellit.dsc_eq_dminus_add_smul_example` already shows that the `BE` configuration occurs, and
the two statements below say that configuration is exactly a pair of mutual partners. What this
route needs is a proof that the partner *always* exists, at every bracketed point and every
above-diagonal path; that is `HJO.Mellit.hasBEPartner_of_isolates` away from the origin.
(`HJO.Mellit.braidValueColouring_eq_dsc_floor` itself is proved by the floored route of
`HJO/Shuffle/MellitThm58Closed.lean`.) `a = 2`, `b = 3` is coprime with `1 < a < b`, so the
instance is in range. -/
theorem hasBEPartner_two_three_one_B :
    HasBEPartner 2 3 1 (7 / 2) (1, 2) (![0, 2, 3] : Heights 2 3 1) := by
  refine ⟨fun _ => ⟨(![0, 3, 3] : Heights 2 3 1), by decide, ?_, by decide⟩, fun h => ?_⟩
  · rw [colouring_thm42_be_witness.1, colouring_thm42_be_witness.2]
  · exact absurd h (by decide)

/-- **The same instance read from the type-`E` side**, which is the other half of
`HJO.Mellit.HasBEPartner` and the one that additionally asks the partner to *sweep* the point: the
type-`B` path `(0,2,3)` does, by `HJO.Mellit.mem_sweptRegion`. See
`HJO.Mellit.hasBEPartner_two_three_one_B`. -/
theorem hasBEPartner_two_three_one_E :
    HasBEPartner 2 3 1 (7 / 2) (1, 2) (![0, 3, 3] : Heights 2 3 1) := by
  refine ⟨fun h => absurd h (by decide),
    fun _ => ⟨(![0, 2, 3] : Heights 2 3 1), by decide, ?_, by decide, by decide⟩⟩
  rw [colouring_thm42_be_witness.1, colouring_thm42_be_witness.2]

end HJO.Mellit

end
