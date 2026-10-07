/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidCompParts
public import HJO.Shuffle.BraidAppendPart
public import HJO.Shuffle.MellitAppend
public meta import HJO.Attr

/-! # The special-braid data of a composition colouring, at the rank the append chain reads

That the braid data of a colouring is special-braid data is proved as
`HJO.Mellit.isSpecialBraidData_braidDataOfColouring`: the pair `(v, α)` of
`HJO.Mellit.braidDataOfColouring` is special-braid data at slope `s_{a,b,N}`. It is stated at rank
`#(colouringNorth y η)`, which is the rank `HJO.Mellit.braidDataOfColouring` is *defined* at.

Every lemma of the append chain reads the data at rank `α.length` — the number of parts of the
return composition — because that is the rank `HJO.Mellit.braidDataOfColouring_snd_hasAboveReturns`
and `HJO.Mellit.braidDataOfColouring_fst_last_ne` are stated at, and because
`HJO.Mellit.braidRep_specialBraid_dplusIter` and `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs`
peel one part off a rank-`k+1` tuple. The two ranks agree by
`HJO.Mellit.card_colouringNorth_hasAboveReturns`, but the identification is a transport across a
dependent type — the tuples live in `Fin n → ℚ` — so it is not something a user of the data can
leave to unification. This file performs it once, in both shapes the chain uses.

## Main results

* `HJO.Mellit.isSpecialBraidData_braidDataOfColouring_hasAboveReturns` — the data of the colouring
  of an above-diagonal path of return composition `α` is special-braid data of rank `α.length`.
* `HJO.Mellit.isSpecialBraidData_braidDataOfColouring_succ` — the same at rank `k + 1`, which is the
  literal shape of the `hdata` hypothesis of every lemma of the append chain.

## Implementation notes

**No hypothesis on `q` or `u`, and none is needed.** Both statements are lattice geometry inside the
colouring: `HJO.Mellit.isSpecialBraidData_braidDataOfColouring` is free of them and
`HJO.Mellit.card_colouringNorth_hasAboveReturns` is a count of lattice points. The side conditions
are `0 < a`, `0 < b`, `0 < N`, `Nat.Coprime a b` and a positive separating admissible level above
`aN`; the standing `1 < a < b` of the section is not used.

**What this does *not* do.** The `hdata` slot is one of six or seven hypotheses at each lemma of the
chain, and it is not the binding one. The others — `hβ`, `hw₀`, `hgap`, `hstart`, `hmove`,
`hfinish`, and `HJO.Braid.IsAppendSetup` itself — are untouched here, and one of them is refuted at
the value the colouring supplies: `HJO.Mellit.braidDataOfColouring_fst_last_ne` shows the last
component's position is strictly below `1 - θ`, which is why the `δ` of
`HJO.Braid.IsAppendSetup` exists at all. The section below records, as elaborated terms rather
than as prose, that `hdata` is discharged at each of the chain's eight lemmas; each such check still
carries every other hypothesis of its lemma.

## References

The definitions and results this file concerns:
`HJO.Mellit.isSpecialBraidData_braidDataOfColouring`, `HJO.Mellit.braidDataOfColouring`,
`HJO.Mellit.braidRep_specialBraid_dplusIter`, `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs`,
`HJO.Mellit.mellitInduction_sweepWitness` and `HJO.Paths.HasAboveReturns`.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### The two ranks -/

/-- **The data of the colouring of a path of return composition `α` is special-braid data of rank
`α.length`.** This is `HJO.Mellit.isSpecialBraidData_braidDataOfColouring` transported along
`HJO.Mellit.card_colouringNorth_hasAboveReturns`; the transport is across the dependent type
`Fin n → ℚ`, so it cannot be left implicit. -/
theorem isSpecialBraidData_braidDataOfColouring_hasAboveReturns (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) (hab : Nat.Coprime a b) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hηN : ((a * N : ℕ) : ℚ) < η) {α : List ℕ}
    {y : Heights a b N} (hret : HasAboveReturns α y) :
    Braid.IsSpecialBraidData (sweepSlope a b N) (sweepTheta a b N) α.length
      (braidDataOfColouring a b N y η α.length).1
      (braidDataOfColouring a b N y η α.length).2 := by
  rw [← card_colouringNorth_hasAboveReturns hηa hηs hab ha hb hN hret]
  exact isSpecialBraidData_braidDataOfColouring ha hb hN hηa hηN hret.1

/-- **The same at rank `k + 1`**, which is the literal shape of the `hdata` hypothesis of every
lemma of the append chain. The composition is nonempty exactly when the rank is a successor. -/
theorem isSpecialBraidData_braidDataOfColouring_succ (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) (hab : Nat.Coprime a b) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hηN : ((a * N : ℕ) : ℚ) < η) {α : List ℕ}
    {y : Heights a b N} (hret : HasAboveReturns α y) {k : ℕ} (hlen : α.length = k + 1) :
    Braid.IsSpecialBraidData (sweepSlope a b N) (sweepTheta a b N) (k + 1)
      (braidDataOfColouring a b N y η (k + 1)).1
      (braidDataOfColouring a b N y η (k + 1)).2 := by
  rw [← hlen]
  exact isSpecialBraidData_braidDataOfColouring_hasAboveReturns ha hb hN hab hηa hηs hηN hret

/-! ### The eight lemmas that carry `hdata`, each with the slot discharged

Each check below is the lemma applied to the data of a composition colouring, with `hdata` supplied
by `HJO.Mellit.isSpecialBraidData_braidDataOfColouring_succ` and *every other hypothesis of the
lemma still a binder*. That a check elaborates is exactly the claim that the lemma's `hdata` slot is
dischargeable at the data `HJO.Mellit.braidDataOfColouring` produces — and that the slot is not
what obstructs the lemma. The conclusions are left to inference: what is being asserted is the
applicability, not a new identity.

The eight lemmas are three in `HJO/Shuffle/MellitAppend.lean`, two in
`HJO/Shuffle/BraidAppendLetters.lean` and three in `HJO/Shuffle/BraidAppendPart.lean`.
-/

section Discharge

open Braid HJO.Sweep

variable {a b N : ℕ} {η : ℚ} {y : Heights a b N} {α : List ℕ} {k : ℕ}
  (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hab : Nat.Coprime a b)
  (hηa : IsAdmissibleLevel η) (hηs : SeparatesDiagonal a b N η)
  (hηN : ((a * N : ℕ) : ℚ) < η) (hret : HasAboveReturns α y) (hlen : α.length = k + 1)

/-- Lemma 1 of 8: `HJO/Shuffle/BraidAppendPart.lean`,
`HJO.Braid.braidWord_specialMoveList_succ_mul_trainDown_one_of_le`. -/
example (hk : 1 ≤ k)
    (hw0 : (braidDataOfColouring a b N y η (k + 1)).1 0 ≤ 1 - sweepTheta a b N)
    (hgap : ∀ (t : Fin k) (i : ℕ), i + 1 < (braidDataOfColouring a b N y η (k + 1)).2 t.succ →
      (nextCrossing (sweepTheta a b N))^[i]
          ((braidDataOfColouring a b N y η (k + 1)).1 t.succ) <
        (braidDataOfColouring a b N y η (k + 1)).1 0 + sweepTheta a b N) :=
  braidWord_specialMoveList_succ_mul_trainDown_one_of_le hk _ _
    (isSpecialBraidData_braidDataOfColouring_succ ha hb hN hab hηa hηs hηN hret hlen) hw0 hgap

/-- Lemma 2 of 8: `HJO/Shuffle/BraidAppendPart.lean`,
`HJO.Braid.braidWord_specialMoveList_succ_mul_trainDown_one`. Its `hw0` is the exact value
`w 0 = 1 - θ`, which `HJO.Mellit.braidDataOfColouring_fst_last_ne` refutes at the last component;
the check is that `hdata` is nevertheless not the obstruction. -/
example (hk : 1 ≤ k)
    (hw0 : (braidDataOfColouring a b N y η (k + 1)).1 0 = 1 - sweepTheta a b N) :=
  braidWord_specialMoveList_succ_mul_trainDown_one hk _ _
    (isSpecialBraidData_braidDataOfColouring_succ ha hb hN hab hηa hηs hηN hret hlen) hw0

/-- Lemma 3 of 8: `HJO/Shuffle/BraidAppendPart.lean`,
`HJO.Braid.specialBraid_eq_conj_phiPlusStar`. -/
example (hk : 1 ≤ k)
    (hw0 : (braidDataOfColouring a b N y η (k + 1)).1 0 ≤ 1 - sweepTheta a b N)
    (hgap : ∀ (t : Fin k) (i : ℕ), i + 1 < (braidDataOfColouring a b N y η (k + 1)).2 t.succ →
      (nextCrossing (sweepTheta a b N))^[i]
          ((braidDataOfColouring a b N y η (k + 1)).1 t.succ) <
        (braidDataOfColouring a b N y η (k + 1)).1 0 + sweepTheta a b N)
    (hstart : ∀ t : Fin k, (braidDataOfColouring a b N y η (k + 1)).1 t.succ <
      (braidDataOfColouring a b N y η (k + 1)).1 0)
    (hfinish : ∀ t : Fin k, (positionPair (sweepTheta a b N)
        ((braidDataOfColouring a b N y η (k + 1)).1 ∘ Fin.succ)
        ((braidDataOfColouring a b N y η (k + 1)).2 ∘ Fin.succ)).2 t <
      (braidDataOfColouring a b N y η (k + 1)).1 0) :=
  specialBraid_eq_conj_phiPlusStar hk _ _
    (isSpecialBraidData_braidDataOfColouring_succ ha hb hN hab hηa hηs hηN hret hlen)
    hw0 hgap hstart hfinish

/-- Lemma 4 of 8: `HJO/Shuffle/BraidAppendLetters.lean`, `HJO.Braid.gap_of_grid` — the
cell lemma that manufactures the `hgap` of the three lemmas above out of the `1/(2D)`-grid. -/
example {δ : ℚ} {n : ℕ} (hn : 0 < n)
    (hgrid : ∀ (t : Fin (k + 1)) (i : ℕ), i < (braidDataOfColouring a b N y η (k + 1)).2 t →
      ∃ m : ℤ, (nextCrossing (sweepTheta a b N))^[i]
        ((braidDataOfColouring a b N y η (k + 1)).1 t) * (n : ℚ) = (m : ℚ))
    (hδ : 0 ≤ δ) (hδn : δ * (n : ℚ) ≤ 1)
    (hw0 : (braidDataOfColouring a b N y η (k + 1)).1 0 = 1 - sweepTheta a b N - δ) :=
  gap_of_grid
    (isSpecialBraidData_braidDataOfColouring_succ ha hb hN hab hηa hηs hηN hret hlen)
    hn hgrid hδ hδn hw0

/-- Lemma 5 of 8: `HJO/Shuffle/BraidAppendLetters.lean`,
`HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs`. -/
example {A : ℕ} {e δ : ℚ} {w : Fin (k + 1) → ℚ}
    (H : IsAppendSetup a b A k e δ (sweepTheta a b N) w) (hk : 1 ≤ k)
    (hβ : (braidDataOfColouring a b N y η (k + 1)).2 0 = A * (a + b) - 1)
    (hw₀ : (braidDataOfColouring a b N y η (k + 1)).1 0 = 1 - sweepTheta a b N - δ)
    (hgap : ∀ (t : Fin k) (i : ℕ), i + 1 < (braidDataOfColouring a b N y η (k + 1)).2 t.succ →
      (nextCrossing (sweepTheta a b N))^[i]
          ((braidDataOfColouring a b N y η (k + 1)).1 t.succ) <
        (braidDataOfColouring a b N y η (k + 1)).1 0 + sweepTheta a b N)
    (hstart : ∀ t : Fin k, (braidDataOfColouring a b N y η (k + 1)).1 t.succ <
      (braidDataOfColouring a b N y η (k + 1)).1 0)
    (hmove : moveTuple (sweepTheta a b N) (braidDataOfColouring a b N y η (k + 1)).1
      ((specialMoveList ((braidDataOfColouring a b N y η (k + 1)).2 ∘ Fin.succ)).map
        Fin.succ) = w) :=
  H.specialBraid_eq_appendRhs hk
    (isSpecialBraidData_braidDataOfColouring_succ ha hb hN hab hηa hηs hηN hret hlen)
    hβ hw₀ hgap hstart hmove

end Discharge

section DischargeOperator

open Braid HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L]

variable {a b N : ℕ} {η : ℚ} {y : Heights a b N} {α : List ℕ} {k : ℕ}
  (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hab : Nat.Coprime a b)
  (hηa : IsAdmissibleLevel η) (hηs : SeparatesDiagonal a b N η)
  (hηN : ((a * N : ℕ) : ℚ) < η) (hret : HasAboveReturns α y) (hlen : α.length = k + 1)

variable {q u r : L} {A : ℕ} {e δ : ℚ} {w : Fin (k + 1) → ℚ}
  (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q)
  (H : IsAppendSetup a b A k e δ (sweepTheta a b N) w)
  (hβ : (braidDataOfColouring a b N y η (k + 1)).2 0 = A * (a + b) - 1)
  (hw₀ : (braidDataOfColouring a b N y η (k + 1)).1 0 = 1 - sweepTheta a b N - δ)
  (hgap : ∀ (t : Fin k) (i : ℕ), i + 1 < (braidDataOfColouring a b N y η (k + 1)).2 t.succ →
    (nextCrossing (sweepTheta a b N))^[i]
        ((braidDataOfColouring a b N y η (k + 1)).1 t.succ) <
      (braidDataOfColouring a b N y η (k + 1)).1 0 + sweepTheta a b N)
  (hstart : ∀ t : Fin k, (braidDataOfColouring a b N y η (k + 1)).1 t.succ <
    (braidDataOfColouring a b N y η (k + 1)).1 0)
  (hmove : moveTuple (sweepTheta a b N) (braidDataOfColouring a b N y η (k + 1)).1
    ((specialMoveList ((braidDataOfColouring a b N y η (k + 1)).2 ∘ Fin.succ)).map Fin.succ) = w)

/-- Lemma 6 of 8: `HJO/Shuffle/MellitAppend.lean`,
`HJO.Mellit.braidRep_specialBraid_dplusIter_aux`. -/
example (h : BraidRepRespects q u r k) (h' : BraidRepRespects q u r (k + 1)) :=
  braidRep_specialBraid_dplusIter_aux (L := L) hq hq1 hqp hr H
    (isSpecialBraidData_braidDataOfColouring_succ ha hb hN hab hηa hηs hηN hret hlen)
    hβ hw₀ hgap hstart hmove h h'

/-- Lemma 7 of 8: `HJO/Shuffle/MellitAppend.lean`,
`HJO.Mellit.braidRep_specialBraid_dplusIter` — the append lemma itself, of which lemma 6 is the
auxiliary form. -/
example :=
  braidRep_specialBraid_dplusIter (L := L) (u := u) hq hq1 hqp hr H
    (isSpecialBraidData_braidDataOfColouring_succ ha hb hN hab hηa hηs hηN hret hlen)
    hβ hw₀ hgap hstart hmove

/-- Lemma 8 of 8: `HJO/Shuffle/MellitAppend.lean`,
`HJO.Mellit.sweepIn_braidRep_specialBraid` — `HJO.Mellit.braidRep_specialBraid_dplusIter` with an
arbitrary replication family `Ω`, the form the recursion clause of `HJO.Mellit.BraidClosedForm`
reads. -/
example {Ω : ℕ → ℕ → ℕ → ((sweepWitness q u a b).W →ₗ[L] (sweepWitness q u a b).W)}
    (hΩ : IsReplicationFamily (sweepWitness q u a b) Ω) :=
  sweepIn_braidRep_specialBraid hq hq1 hqp hr hΩ H
    (isSpecialBraidData_braidDataOfColouring_succ ha hb hN hab hηa hηs hηN hret hlen)
    hβ hw₀ hgap hstart hmove

end DischargeOperator

end HJO.Mellit

end
