/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepShiftPropagate
public import HJO.Shuffle.SweepAppendBandRounds
public import HJO.Shuffle.SweepEventCounts
public import HJO.Shuffle.SweepPositions
public import HJO.Shuffle.ColouringStep
public meta import HJO.Attr

/-!
# The staircase fits: the layer propagation's width side condition, discharged

`HJO.Mellit.exists_layerWord_shiftAux` transports a whole base layer of a round past the shift
`Σ_δ = HJO.Sweep.shiftAux`, at the price of one hypothesis on the widths: at each event `P` of the
layer the staircase accumulated by the events already applied must fit under the index the
extension's operator reads at `P`. This file proves that hypothesis is **automatic**, and restates
the propagation without it.

## The condition, and why the stated one is not it

The staircase arriving at `P` has one block per type-`A`-or-`C` event applied before `P`, so what
the induction consumes is

* `#{type-A-or-C events applied before P} ≤ sweepWidth z P` at a type-`A` event, and
* `#{type-A-or-C events applied before P} + 1 ≤ sweepWidth z P` at a type-`B` or type-`C` event,

and **nothing at all** at types `D` and `E`, whose operators are scalars. The shift `δ` cancels from
both: the extension reads at `sweepWidth z P + δ` and the staircase's top letter carries the same
`δ`. So the condition is parameter-free — no `a`, no `A`, no `q`, no `u`, no coprimality.

The hypothesis `exists_layerWord_shiftAux` actually asks, namely `#(suffix) + 1 ≤ sweepWidth z P` at
*every* event, is strictly stronger and is **false**: it counts every event rather than the
type-`A`-or-`C` ones, and it asks for the `+ 1` at type `A`, where the width can be `0`. On the
`1 × 1` rectangle, whose only above-diagonal path has `ŷ = (0, 1)`, the point `(0, 1)` is the layer
of excess `1`, it is a type-`A` event, and `sweepWidth z (0,1) = 0` — the single north step `(0,0)`
has rank `0`, which the half-open window `(rk(0,1) - ω, rk(0,1)] = (0, 2]` misses at its open end.
So `#(suffix) + 1 = 1 > 0`, and the hypothesis fails on the worked instance the band identity was
closed at. `HJO.Mellit.exists_layerWord_shiftAux_of_sorted` below is the statement with the sharp
condition discharged instead.

## How the sharp condition is proved

Inside a round the diagonal excess is constant, so `HJO.Mellit.pointRank` is `C·e + x` with `C` the
same integer for every point of the layer: the rank order **is** the abscissa order, which is
`HJO.Mellit.sortByRank_pairwise_fst_lt`, and the events applied before `P` are exactly the layer's
points of higher abscissa. Against those stand the live north steps to the right of `P`, counted by
`HJO.Paths.sweepRight`, and the comparison is an injection:

* a layer point `Q` of type `A` or `C` lies strictly above the foot of its own column, so the unit
  segment `(Q.1, Q.2 - 1)` below it is a north step of `z`
  (`HJO.Paths.mem_northSteps_pred_of_eventType_A_or_C`);
* its excess is that of `Q` less `a`, hence that of `P` less `a`, which is the closed end of the
  window `[e - a, e)` of `HJO.Paths.mem_liveSteps_iff_of_lt_fst` — so it is live at `P`, and it is
  counted to the right because its column is `Q`'s;
* distinct layer points have distinct abscissae, so the map is injective.

That is `HJO.Mellit.acCount_le_sweepRight`, and it settles type `A`. The extra unit at types `B` and
`C` is the point's own step: at both of those the outgoing letter is north, so `P` *is* a north step
of `z`, it is live at itself, and its column is not strictly to the right of itself — so
`sweepRight z P < sweepWidth z P` (`HJO.Paths.sweepRight_lt_sweepWidth_of_eventType_B_or_C`).

The width does **not** obey a `±1` recursion along a layer: a round reorders the sweep, consecutive
points of one excess level are `(a, b)` apart, and the events between them belong to other levels.
The abscissa/`sweepRight` comparison replaces that, and needs only `0 < a * N`.

## Main results

* `HJO.Paths.mem_northSteps_pred_of_eventType_A_or_C`,
  `HJO.Paths.mem_northSteps_of_eventType_B_or_C` and
  `HJO.Paths.sweepRight_lt_sweepWidth_of_eventType_B_or_C`: the two north steps the comparison
  needs, and the strict inequality at `B` and `C`.
* `HJO.Mellit.acCount`: the number of type-`A`-or-`C` events in a list of points — the height of the
  staircase the layer accumulates.
* `HJO.Mellit.acCount_le_sweepRight`: **the side condition.** The staircase arriving at `P` is no
  taller than the live steps to the right of `P`.
* `HJO.Mellit.sortByRank_pairwise_fst_lt`: inside one excess level the rank listing is the abscissa
  listing.
* `HJO.Mellit.exists_layerWord_shiftAux_of_sorted`: **the layer propagation with no width
  hypothesis**, for any list of base points of one excess level listed by increasing abscissa, and
  with the staircase's height named as `acCount` rather than merely bounded by `#ℓ`.
* `HJO.Mellit.not_layerWidth_oneOneOne`: **the refutation of the stated `hwid`**, on the `1 × 1`
  rectangle, whose round of excess `1` is the single type-`A` point `(0, 1)` of width `0`.
* `HJO.Mellit.exists_layerWord_shiftAux_of_finset` and
  `HJO.Mellit.exists_layerWord_shiftAux_round`: the same for the rank listing of a level set, and
  for the base layer `{P : rk P > η, exc P = e, P.1 < aN}` of a round that
  `HJO.Mellit.roundSweepWord_split_fst` cuts out.
* `HJO.Mellit.exists_baseRound_shiftAux`: **the capstone.** At a separating level the extension's
  base layer of round `e` transports to the base's own `HJO.Mellit.roundSweepWord`.

`q ≠ 0` survives, and only to add the `ℤ`-exponents of rules `C` and `D`, whose scalars are inverse
to one another. Nothing here reads `u`, `q ≠ 1`, coprimality, or any bound relating `a` to `b`.
-/

@[expose] public section

noncomputable section

open Finset HJO.ParkingFunctions

namespace HJO.Paths

variable {a b N : ℕ}

/-! ### The two north steps the width comparison needs -/

/-- **Below a type-`A`-or-`C` event sits a north step.** At both of those types the point lies
strictly above the foot `ŷ_x` of its own column, and being swept it lies weakly below the top
`ŷ_{x+1}`; so the unit segment from `(x, k-1)` to `(x, k)` is a north step of the path. -/
theorem mem_northSteps_pred_of_eventType_A_or_C {z : Heights a b N} {Q : ℕ × ℕ}
    (hQ : Q ∈ sweptRegion z) (hQ1 : Q.1 < a * N)
    (hev : eventType z Q = EventType.A ∨ eventType z Q = EventType.C) :
    (Q.1, Q.2 - 1) ∈ northSteps z := by
  have hht : ht z Q.1 < Q.2 := by
    rcases hev with h | h
    · exact (eventType_eq_A_iff.1 h).1
    · exact (eventType_eq_C_iff.1 h).1
  have htop : Q.2 ≤ ht z (Q.1 + 1) := (mem_sweptRegion.1 hQ).2.2
  exact mem_northSteps_iff.2 ⟨hQ1, by simp only; omega, by simp only; omega⟩

/-- **A type-`B`-or-`C` event is itself a north step.** At both of those types the outgoing letter
is north, which is exactly `ŷ_x ≤ k < ŷ_{x+1}` together with `x < aN`. -/
theorem mem_northSteps_of_eventType_B_or_C {z : Heights a b N} {P : ℕ × ℕ}
    (hev : eventType z P = EventType.B ∨ eventType z P = EventType.C) :
    P ∈ northSteps z := by
  rcases hev with h | h
  · obtain ⟨h1, h2, h3⟩ := eventType_eq_B_iff.1 h
    exact mem_northSteps_iff.2 ⟨h2, by omega, h3⟩
  · obtain ⟨h1, h2, h3⟩ := eventType_eq_C_iff.1 h
    exact mem_northSteps_iff.2 ⟨h2, by omega, h3⟩

/-- The live steps to the right of a point are live at it. -/
theorem sweepRight_le_sweepWidth (z : Heights a b N) (P : ℕ × ℕ) :
    sweepRight z P ≤ sweepWidth z P := Finset.card_filter_le _ _

/-- **At a type-`B`-or-`C` event the width strictly exceeds the count to the right.** The point's
own step is live at it — that is `HJO.Paths.mem_liveSteps_iff_eq_of_fst_eq` — and its column is not
strictly to the right of itself, so `HJO.Paths.sweepRight` misses it. This is the extra unit rules
`B` and `C` consume beyond what the staircase already occupies. -/
@[hjo "lem_sweep_layer_width_bc"]
theorem sweepRight_lt_sweepWidth_of_eventType_B_or_C {z : Heights a b N} {P : ℕ × ℕ}
    (hev : eventType z P = EventType.B ∨ eventType z P = EventType.C) :
    sweepRight z P < sweepWidth z P := by
  have hP : P ∈ northSteps z := mem_northSteps_of_eventType_B_or_C hev
  have hPlive : P ∈ liveSteps z P := (mem_liveSteps_iff_eq_of_fst_eq hP rfl).2 rfl
  have hsplit : #{u ∈ liveSteps z P | P.1 < u.1} + #{u ∈ liveSteps z P | ¬ P.1 < u.1}
      = #(liveSteps z P) := Finset.card_filter_add_card_filter_not _
  have hpos : 0 < #{u ∈ liveSteps z P | ¬ P.1 < u.1} :=
    Finset.card_pos.2 ⟨P, Finset.mem_filter.2 ⟨hPlive, by omega⟩⟩
  rw [sweepRight, sweepWidth]
  omega

end HJO.Paths

namespace HJO.Mellit

open HJO.Paths HJO.Sweep

variable {a b N : ℕ}

/-! ### The staircase fits under the width -/

/-- Dropping a point by one unit lowers its diagonal excess by `a`. -/
theorem diagExcess_pred_snd {Q : ℕ × ℕ} (hQ : 1 ≤ Q.2) :
    diagExcess a b (Q.1, Q.2 - 1) = diagExcess a b Q - a := by
  simp only [diagExcess]
  have hcast : ((Q.2 - 1 : ℕ) : ℤ) = (Q.2 : ℤ) - 1 := by
    have := Nat.cast_sub (R := ℤ) hQ
    simpa using this
  rw [hcast]
  ring

/-- **THE SIDE CONDITION, as a comparison of a level set with the live steps to the right.** Among
the points of one diagonal excess level lying strictly to the right of `P`, those of type `A` or `C`
are at most the live north steps strictly to the right of `P`.

The injection is `Q ↦ (Q.1, Q.2 - 1)`, the north step below `Q`: it exists because a type-`A`-or-`C`
event lies above the foot of its column, it is live at `P` because its excess is that of `P` less
`a`, the closed end of the window of `HJO.Paths.mem_liveSteps_iff_of_lt_fst`, and it is counted to
the right because its column is `Q`'s. Injectivity is that one excess level meets each column once.

Nothing here reads the level, the path's shape beyond `Q ∈ Sw(z)`, or any parameter but `0 < a` and
`0 < N`. -/
@[hjo "lem_sweep_layer_width"]
theorem card_filter_ac_le_sweepRight (hN : 0 < N) (ha : 0 < a) {z : Heights a b N} {P : ℕ × ℕ}
    (hP1 : P.1 ≤ a * N) {S : Finset (ℕ × ℕ)}
    (hSreg : ∀ Q ∈ S, Q ∈ sweptRegion z) (hSlow : ∀ Q ∈ S, Q.1 < a * N)
    (hSlt : ∀ Q ∈ S, P.1 < Q.1) (hSexc : ∀ Q ∈ S, diagExcess a b Q = diagExcess a b P) :
    #{Q ∈ S | eventType z Q = EventType.A ∨ eventType z Q = EventType.C}
      ≤ sweepRight z P := by
  rw [sweepRight]
  refine Finset.card_le_card_of_injOn (fun Q => (Q.1, Q.2 - 1)) ?_ ?_
  · intro Q hQ
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hQ
    obtain ⟨hQS, hQev⟩ := hQ
    have hht : ht z Q.1 < Q.2 := by
      rcases hQev with h | h
      · exact (eventType_eq_A_iff.1 h).1
      · exact (eventType_eq_C_iff.1 h).1
    have hns : (Q.1, Q.2 - 1) ∈ northSteps z :=
      mem_northSteps_pred_of_eventType_A_or_C (hSreg Q hQS) (hSlow Q hQS) hQev
    have hexc : diagExcess a b (Q.1, Q.2 - 1) = diagExcess a b P - a := by
      rw [diagExcess_pred_snd (by omega), hSexc Q hQS]
    have hlt : P.1 < ((Q.1, Q.2 - 1) : ℕ × ℕ).1 := hSlt Q hQS
    have haz : (0 : ℤ) < a := by exact_mod_cast ha
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨?_, hlt⟩)
    exact (mem_liveSteps_iff_of_lt_fst hN hns hP1 hlt).2 ⟨by omega, by omega⟩
  · intro Q hQ Q' hQ' h
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hQ hQ'
    simp only [Prod.mk.injEq] at h
    have h1 : Q.1 = Q'.1 := h.1
    have hE := hSexc Q hQ.1
    have hE' := hSexc Q' hQ'.1
    simp only [diagExcess, h1] at hE hE'
    have haz : (0 : ℤ) < a := by exact_mod_cast ha
    have h2 : Q.2 = Q'.2 := by
      have hmul : (a : ℤ) * Q.2 = (a : ℤ) * Q'.2 := by omega
      have := mul_left_cancel₀ (by omega : (a : ℤ) ≠ 0) hmul
      exact_mod_cast this
    exact Prod.ext h1 h2

/-! ### The height of the staircase a layer accumulates -/

/-- The number of type-`A`-or-`C` events of `z` in a list of lattice points: the height of the
staircase `HJO.Sweep.stairWord` that the layer's propagation accumulates, since exactly those two
rules emit a block. -/
@[hjo "def_sweep_ac_count"]
def acCount (z : Heights a b N) (ℓ : List (ℕ × ℕ)) : ℕ :=
  ℓ.countP fun Q => decide (eventType z Q = EventType.A ∨ eventType z Q = EventType.C)

@[simp] theorem acCount_nil (z : Heights a b N) : acCount z [] = 0 := rfl

theorem acCount_cons_of_ac {z : Heights a b N} {x : ℕ × ℕ} (ℓ : List (ℕ × ℕ))
    (hx : eventType z x = EventType.A ∨ eventType z x = EventType.C) :
    acCount z (x :: ℓ) = acCount z ℓ + 1 := by
  simp [acCount, hx]

theorem acCount_cons_of_not_ac {z : Heights a b N} {x : ℕ × ℕ} (ℓ : List (ℕ × ℕ))
    (hx : ¬ (eventType z x = EventType.A ∨ eventType z x = EventType.C)) :
    acCount z (x :: ℓ) = acCount z ℓ := by
  simp [acCount, hx]

theorem acCount_le_length (z : Heights a b N) (ℓ : List (ℕ × ℕ)) :
    acCount z ℓ ≤ ℓ.length := List.countP_le_length

/-- **THE SIDE CONDITION, in the form the induction consumes.** For a list of points of one excess
level all standing strictly to the right of `P`, the staircase they accumulate is no taller than the
live steps to the right of `P`. This is `HJO.Mellit.card_filter_ac_le_sweepRight` read along a list,
the listing being duplicate-free. -/
@[hjo "lem_sweep_layer_width"]
theorem acCount_le_sweepRight (hN : 0 < N) (ha : 0 < a) {z : Heights a b N} {P : ℕ × ℕ}
    (hP1 : P.1 ≤ a * N) {t : List (ℕ × ℕ)} (hnd : t.Nodup)
    (hreg : ∀ Q ∈ t, Q ∈ sweptRegion z) (hlow : ∀ Q ∈ t, Q.1 < a * N)
    (hlt : ∀ Q ∈ t, P.1 < Q.1) (hexc : ∀ Q ∈ t, diagExcess a b Q = diagExcess a b P) :
    acCount z t ≤ sweepRight z P := by
  classical
  have hcard : acCount z t
      = #{Q ∈ t.toFinset | eventType z Q = EventType.A ∨ eventType z Q = EventType.C} := by
    rw [acCount, List.countP_eq_length_filter,
      ← List.toFinset_card_of_nodup (hnd.filter _), List.toFinset_filter]
    congr 1
    ext Q
    simp
  rw [hcard]
  exact card_filter_ac_le_sweepRight hN ha hP1
    (fun Q hQ => hreg Q (List.mem_toFinset.1 hQ))
    (fun Q hQ => hlow Q (List.mem_toFinset.1 hQ))
    (fun Q hQ => hlt Q (List.mem_toFinset.1 hQ))
    (fun Q hQ => hexc Q (List.mem_toFinset.1 hQ))

/-! ### The layer propagation without its width hypothesis -/

section Layer

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {A : ℕ}
  {z : Heights a b N} {w : Heights a b A}

/-- **THE LAYER PROPAGATION, WITH THE WIDTH SIDE CONDITION DISCHARGED.** For a list `ℓ` of swept
base points of one diagonal excess level, listed by increasing abscissa — which by
`HJO.Mellit.roundSweepWord_split_fst` and `HJO.Mellit.sortByRank_pairwise_fst_lt` is what a round's
base layer is —

`(∏_{P ∈ ℓ} O^{ext}_P)(g·Σ_δF) = q^s · S_{0,m}(g·Σ_δ((∏_{P ∈ ℓ} O^{base}_P)F))`

with `m = HJO.Mellit.acCount z ℓ` the number of type-`A`-or-`C` events of the layer and `s` the
integer `δ·(#D − #C)`.

This is `HJO.Mellit.exists_layerWord_shiftAux` with **no hypothesis on the widths** — its `hwid`, as
well as being stronger than what the induction consumes, is false at a type-`A` event of width `0`,
of which the `1 × 1` rectangle already has one. What replaces it is the geometry of a layer: at each
event the staircase arriving is `HJO.Mellit.acCount_le_sweepRight`-bounded by the live steps to the
right, and at types `B` and `C` the point's own step gives the extra unit. The height `m` is now
named rather than merely bounded by `#ℓ`, which is what makes the bound available at every step of
the induction.

Nothing on `q` but `q ≠ 0`, which only adds the exponents of rules `C` and `D`; and `0 < a` is not
assumed, being forced by any point of the layer. -/
@[hjo "lem_sweep_layer_shift_append"]
theorem exists_layerWord_shiftAux_of_sorted (hq : q ≠ 0) (hz : IsAboveDiagonal z)
    (hw : IsAboveDiagonal w) (hN : 0 < N) (δ : ℕ) {g : Total L} (hgaux : g ∈ auxSubalg L)
    (hgp : g ∈ piece L δ) (F : Total L) :
    ∀ ℓ : List (ℕ × ℕ), (∀ P ∈ ℓ, P ∈ sweptRegion z) → (∀ P ∈ ℓ, P.1 < a * N) →
      (∀ P ∈ ℓ, #(tailLiveSteps w (diagExcess a b P)) = δ) →
      ℓ.Pairwise (fun P Q => P.1 < Q.1) →
      (∀ P ∈ ℓ, ∀ Q ∈ ℓ, diagExcess a b P = diagExcess a b Q) →
      ∃ s : ℤ,
        (ℓ.map (sweepOperator q u (appendHeights z w))).prod (g * shiftAux L δ F)
          = q ^ s • stairWord q δ 0 (acCount z ℓ)
              (g * shiftAux L δ ((ℓ.map (sweepOperator q u z)).prod F)) := by
  intro ℓ
  induction ℓ with
  | nil => intro _ _ _ _ _; exact ⟨0, by simp⟩
  | cons x t ih =>
    intro hreg hlow hδ hsort hexc
    have hsortt : t.Pairwise (fun P Q => P.1 < Q.1) := (List.pairwise_cons.1 hsort).2
    have hxlt : ∀ Q ∈ t, x.1 < Q.1 := (List.pairwise_cons.1 hsort).1
    obtain ⟨s, heq⟩ := ih
      (fun P hP => hreg P (List.mem_cons_of_mem _ hP))
      (fun P hP => hlow P (List.mem_cons_of_mem _ hP))
      (fun P hP => hδ P (List.mem_cons_of_mem _ hP)) hsortt
      (fun P hP Q hQ => hexc P (List.mem_cons_of_mem _ hP) Q (List.mem_cons_of_mem _ hQ))
    have hxmem : x ∈ x :: t := List.mem_cons_self ..
    have hlowx : x.1 < a * N := hlow x hxmem
    have hδx : #(tailLiveSteps w (diagExcess a b x)) = δ := hδ x hxmem
    have ha : 0 < a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · exact absurd hlowx (by simp [h])
      · exact h
    have hndt : t.Nodup := hsortt.imp (fun {P Q} h => by intro hPQ; rw [hPQ] at h; omega)
    have hm : acCount z t ≤ sweepRight z x :=
      acCount_le_sweepRight hN ha hlowx.le hndt
        (fun Q hQ => hreg Q (List.mem_cons_of_mem _ hQ))
        (fun Q hQ => hlow Q (List.mem_cons_of_mem _ hQ)) hxlt
        (fun Q hQ => (hexc x hxmem Q (List.mem_cons_of_mem _ hQ)).symm)
    have hmw : acCount z t ≤ sweepWidth z x := hm.trans (sweepRight_le_sweepWidth z x)
    have hwext : sweepWidth (appendHeights z w) x = sweepWidth z x + δ := by
      rw [sweepWidth_appendHeights_eq hz hw hN hlowx, hδx]
    have hgpx : g ∈ piece L (#(tailLiveSteps w (diagExcess a b x))) := by rw [hδx]; exact hgp
    have htyp : eventType (appendHeights z w) x = eventType z x :=
      eventType_appendHeights (by omega)
    have hbA : acCount z t + δ ≤ sweepWidth (appendHeights z w) x := by rw [hwext]; omega
    set Y : Total L := (t.map (sweepOperator q u z)).prod F with hY
    have hLc : ((x :: t).map (sweepOperator q u (appendHeights z w))).prod (g * shiftAux L δ F)
        = sweepOperator q u (appendHeights z w) x
            ((t.map (sweepOperator q u (appendHeights z w))).prod (g * shiftAux L δ F)) := by
      rw [List.map_cons, List.prod_cons]; rfl
    have hRc : ((x :: t).map (sweepOperator q u z)).prod F = sweepOperator q u z x Y := by
      rw [List.map_cons, List.prod_cons, hY]; rfl
    cases hevx : eventType z x with
    | A =>
      refine ⟨s, ?_⟩
      have hac : acCount z (x :: t) = acCount z t + 1 := acCount_cons_of_ac t (Or.inl hevx)
      have hev := sweepOperator_shiftAux_appendHeights_A (q := q) (u := u) hz hw hN hlowx hevx
        hgaux hgpx Y
      rw [hδx] at hev
      rw [hac, hLc, heq, map_smul,
        sweepOperator_stairWord_A (htyp.trans hevx) hbA, hev,
        stairWord_succ_shift_zero_apply, hRc]
    | B =>
      refine ⟨s, ?_⟩
      have hac : acCount z (x :: t) = acCount z t := acCount_cons_of_not_ac t (by simp [hevx])
      have hlt : acCount z t < sweepWidth z x :=
        hm.trans_lt (sweepRight_lt_sweepWidth_of_eventType_B_or_C (Or.inl hevx))
      have hbB : acCount z t + δ + 1 ≤ sweepWidth (appendHeights z w) x := by rw [hwext]; omega
      have hev := sweepOperator_shiftAux_appendHeights_B (q := q) (u := u) hz hw hN hlowx
        (by omega) hevx hgaux hgpx Y
      rw [hδx] at hev
      rw [hac, hLc, heq, map_smul,
        sweepOperator_stairWord_B (htyp.trans hevx) hbB, hev, hRc]
    | C =>
      refine ⟨s - δ, ?_⟩
      have hac : acCount z (x :: t) = acCount z t + 1 := acCount_cons_of_ac t (Or.inr hevx)
      have hlt : acCount z t < sweepWidth z x :=
        hm.trans_lt (sweepRight_lt_sweepWidth_of_eventType_B_or_C (Or.inr hevx))
      have hbB : acCount z t + δ + 1 ≤ sweepWidth (appendHeights z w) x := by rw [hwext]; omega
      have hev := sweepOperator_shiftAux_appendHeights_C (q := q) (u := u) hq hz hw hN hlowx
        (by omega) hevx hgaux hgpx Y
      rw [hδx] at hev
      rw [hac, hLc, heq, map_smul,
        sweepOperator_stairWord_C (htyp.trans hevx) hbB, hev, map_smul,
        stairWord_succ_shift_zero_apply, hRc, smul_smul, ← zpow_add₀ hq]
      congr 2
    | D =>
      refine ⟨s + δ, ?_⟩
      have hac : acCount z (x :: t) = acCount z t := acCount_cons_of_not_ac t (by simp [hevx])
      have hev := sweepOperator_shiftAux_appendHeights_D (q := q) (u := u) hz hw hN hlowx hevx g Y
      rw [hδx] at hev
      rw [hac, hLc, heq, map_smul, sweepOperator_stairWord_D (htyp.trans hevx), hev, map_smul,
        hRc, smul_smul, ← zpow_natCast q δ, ← zpow_add₀ hq]
    | E =>
      refine ⟨s, ?_⟩
      have hac : acCount z (x :: t) = acCount z t := acCount_cons_of_not_ac t (by simp [hevx])
      have hev := sweepOperator_shiftAux_appendHeights_E (q := q) (u := u) (z := z) (w := w)
        (by omega) hevx g Y
      rw [hδx] at hev
      rw [hac, hLc, heq, map_smul, sweepOperator_stairWord_E (htyp.trans hevx), hev, hRc]

end Layer

/-! ### The rank listing of a layer is its abscissa listing -/

/-- **Inside one diagonal excess level the rank listing is the abscissa listing.** The rank
`HJO.Mellit.pointRank` is the lexicographic key `(excess, abscissa)` of
`HJO.Mellit.abovePointRank_le_iff`, so on a set of constant excess it reduces to the abscissa; the
listing being duplicate-free and an excess level meeting each column once, the order is strict.

This is the hypothesis of `HJO.Mellit.exists_layerWord_shiftAux_of_sorted` that
`HJO.Mellit.roundSweepWord_split_fst` was pointing at: the events of a round applied before `P` are
exactly the layer's points of higher abscissa. -/
@[hjo "lem_sweep_layer_rank_abscissa"]
theorem sortByRank_pairwise_fst_lt (hN : 0 < N) (ha : 0 < a) {S : Finset (ℕ × ℕ)} {e : ℤ}
    (hSb : ∀ Q ∈ S, Q.1 ≤ a * N) (hSe : ∀ Q ∈ S, diagExcess a b Q = e) :
    (sortByRank a b N S).Pairwise (fun P Q => P.1 < Q.1) := by
  refine (List.pairwise_and_iff.2
    ⟨sortByRank_pairwise a b N S, sortByRank_nodup a b N S⟩).imp_of_mem ?_
  intro P Q hP hQ h
  obtain ⟨hle, hne⟩ := h
  have hPS : P ∈ S := mem_sortByRank.1 hP
  have hQS : Q ∈ S := mem_sortByRank.1 hQ
  have hEP := hSe P hPS
  have hEQ := hSe Q hQS
  simp only [diagExcess] at hEP hEQ
  simp only [pointRank, abovePointRank_le_iff hN (hSb P hPS) (hSb Q hQS)] at hle
  rw [hEP, hEQ] at hle
  have hPle : P.1 ≤ Q.1 := by
    rcases hle with h | h
    · exact absurd h (lt_irrefl e)
    · exact h.2
  rcases eq_or_lt_of_le hPle with heq | hlt
  · exfalso
    refine hne (Prod.ext heq ?_)
    have hb : (b : ℤ) * P.1 = (b : ℤ) * Q.1 := by rw [heq]
    have hmul : (a : ℤ) * P.2 = (a : ℤ) * Q.2 := by linarith
    have := mul_left_cancel₀ (Nat.cast_ne_zero.2 ha.ne' : (a : ℤ) ≠ 0) hmul
    exact_mod_cast this
  · exact hlt

section LayerFinset

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {A : ℕ}
  {z : Heights a b N} {w : Heights a b A}

/-- **The layer propagation for a level set, no width hypothesis.** The rank listing of a set of
swept base points of one diagonal excess level transports past `Σ_δ`, the discrepancy being the
staircase of height `HJO.Mellit.acCount` and a power of `q`.

`0 < a` is not assumed: at `a = 0` no point has abscissa below `a * N`, so the set is empty. -/
theorem exists_layerWord_shiftAux_of_finset (hq : q ≠ 0) (hz : IsAboveDiagonal z)
    (hw : IsAboveDiagonal w) (hN : 0 < N) (δ : ℕ) {g : Total L}
    (hgaux : g ∈ auxSubalg L) (hgp : g ∈ piece L δ) (F : Total L) {S : Finset (ℕ × ℕ)} {e : ℤ}
    (hSreg : ∀ P ∈ S, P ∈ sweptRegion z) (hSlow : ∀ P ∈ S, P.1 < a * N)
    (hSe : ∀ P ∈ S, diagExcess a b P = e) (hδ : #(tailLiveSteps w e) = δ) :
    ∃ s : ℤ,
      ((sortByRank a b N S).map (sweepOperator q u (appendHeights z w))).prod
          (g * shiftAux L δ F)
        = q ^ s • stairWord q δ 0 (acCount z (sortByRank a b N S))
            (g * shiftAux L δ (((sortByRank a b N S).map (sweepOperator q u z)).prod F)) := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · have hempty : S = ∅ :=
      Finset.eq_empty_of_forall_notMem fun P hP => absurd (hSlow P hP) (by simp [ha])
    subst hempty
    exact ⟨0, by simp [sortByRank_empty]⟩
  · exact exists_layerWord_shiftAux_of_sorted hq hz hw hN δ hgaux hgp F _
      (fun P hP => hSreg P (mem_sortByRank.1 hP))
      (fun P hP => hSlow P (mem_sortByRank.1 hP))
      (fun P hP => by rw [hSe P (mem_sortByRank.1 hP)]; exact hδ)
      (sortByRank_pairwise_fst_lt hN ha (fun Q hQ => (hSlow Q hQ).le) hSe)
      (fun P hP Q hQ => by
        rw [hSe P (mem_sortByRank.1 hP), hSe Q (mem_sortByRank.1 hQ)])

/-- **The base layer of a round of an extension transports, with nothing assumed about widths.**
This is the layer `HJO.Mellit.roundSweepWord_split_fst` cuts out at `c = a * N`: the round-`e`
points above the level `η` whose abscissa is the base's. Only `q ≠ 0` and `0 < N` survive. -/
theorem exists_layerWord_shiftAux_round (hq : q ≠ 0) (hz : IsAboveDiagonal z)
    (hw : IsAboveDiagonal w) (hN : 0 < N) (δ : ℕ) {g : Total L}
    (hgaux : g ∈ auxSubalg L) (hgp : g ∈ piece L δ) (F : Total L) (η : ℚ) (e : ℤ)
    (hδ : #(tailLiveSteps w e) = δ) :
    ∃ s : ℤ,
      ((sortByRank a b N {P ∈ sweptAbove z η | diagExcess a b P = e ∧ P.1 < a * N}).map
            (sweepOperator q u (appendHeights z w))).prod (g * shiftAux L δ F)
        = q ^ s • stairWord q δ 0
            (acCount z (sortByRank a b N
              {P ∈ sweptAbove z η | diagExcess a b P = e ∧ P.1 < a * N}))
            (g * shiftAux L δ
              (((sortByRank a b N {P ∈ sweptAbove z η | diagExcess a b P = e ∧ P.1 < a * N}).map
                (sweepOperator q u z)).prod F)) :=
  exists_layerWord_shiftAux_of_finset hq hz hw hN δ hgaux hgp F
    (fun _ hP => (Finset.mem_filter.1 (Finset.mem_filter.1 hP).1).1)
    (fun _ hP => (Finset.mem_filter.1 hP).2.2)
    (fun _ hP => (Finset.mem_filter.1 hP).2.1) hδ


/-- **THE BASE LAYER OF A ROUND OF AN EXTENSION TRANSPORTS TO THE BASE'S OWN ROUND WORD.** The
extension's round-`e` events of base abscissa, applied to `g·Σ_δF`, are a power of `q` times a
staircase applied to `Σ_δ` of the base's own `HJO.Mellit.roundSweepWord` applied to `F`.

Three earlier facts glue together here: `HJO.Mellit.baseRoundWord_appendHeights` identifies the
extension's base layer with the base's own round listing, still read at the extension's operators;
`HJO.Paths.sweptAbove_filter_lt_appendHeights` supplies the abscissa bound, a separating level
leaving the corner column to the tail; and
`HJO.Mellit.exists_layerWord_shiftAux_of_finset` transports it, with the width side condition
discharged. No hypothesis on the widths survives, and the only thing asked of `q` is `q ≠ 0`. -/
theorem exists_baseRound_shiftAux (hq : q ≠ 0) (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w)
    (ha : 0 < a) (hN : 0 < N) (δ : ℕ) {g : Total L} (hgaux : g ∈ auxSubalg L)
    (hgp : g ∈ piece L δ) (F : Total L) {η η' : ℚ}
    (hη : SeparatesDiagonal a b (N + A) η) (hη' : SeparatesDiagonal a b N η') (e : ℤ)
    (hδ : #(tailLiveSteps w e) = δ) :
    ∃ s : ℤ,
      ((sortByRank a b (N + A) {P ∈ sweptAbove (appendHeights z w) η |
            diagExcess a b P = e ∧ P.1 < a * N}).map
          (sweepOperator q u (appendHeights z w))).prod (g * shiftAux L δ F)
        = q ^ s • stairWord q δ 0
            (acCount z (sortByRank a b N {P ∈ sweptAbove z η' | diagExcess a b P = e}))
            (g * shiftAux L δ (roundSweepWord q u z η' e F)) := by
  have hbound : ∀ P ∈ sweptAbove z η', P.1 < a * N := by
    intro P hP
    rw [← sweptAbove_filter_lt_appendHeights (z := z) (w := w) hη hη'] at hP
    exact (Finset.mem_filter.1 hP).2
  rw [baseRoundWord_appendHeights (q := q) (u := u) ha hN hη hη' e]
  exact exists_layerWord_shiftAux_of_finset hq hz hw hN δ hgaux hgp F
    (fun _ hP => (Finset.mem_filter.1 (Finset.mem_filter.1 hP).1).1)
    (fun _ hP => hbound _ (Finset.mem_filter.1 hP).1)
    (fun _ hP => (Finset.mem_filter.1 hP).2) hδ

end LayerFinset

/-! ### The stated side condition is false, on the smallest rectangle there is -/

section Refutation

/-- The unique above-diagonal path of the `1 × 1` rectangle, `ŷ = (0, 1)`. -/
def pathOneOne : Heights 1 1 1 := fun i => i

theorem isAboveDiagonal_pathOneOne : IsAboveDiagonal pathOneOne := by decide

/-- **A type-`A` event of width zero.** The point `(0, 1)` is swept, has diagonal excess `1` and
abscissa below `a * N = 1`, so it is a whole base layer; the path's one north step is `(0, 0)`, of
rank `0`, and the half-open live window at `(0, 1)` is `(0, 2]`, which misses it. -/
theorem sweepWidth_pathOneOne_eq_zero : sweepWidth pathOneOne (0, 1) = 0 := by decide

theorem eventType_pathOneOne_eq_A : eventType pathOneOne (0, 1) = EventType.A := by decide

/-- **The round of excess `1` is the single point `(0, 1)`.** Read at the level `0`, which the rank
`2` of `(0, 1)` clears. -/
theorem round_pathOneOne :
    {P ∈ sweptAbove pathOneOne 0 | diagExcess 1 1 P = 1 ∧ P.1 < 1 * 1}
      = {((0, 1) : ℕ × ℕ)} := by decide

/-- **THE STATED WIDTH HYPOTHESIS IS FALSE.** The side condition
`∀ v r P, ℓ = v ++ P :: r → #r + 1 ≤ sweepWidth z P` of
`HJO.Mellit.exists_layerWord_shiftAux` fails on the base layer of the excess-`1` round of the
`1 × 1` rectangle — a one-point layer, so the suffix is empty and the hypothesis asks only
`1 ≤ sweepWidth`, which `HJO.Mellit.sweepWidth_pathOneOne_eq_zero` denies.

So that theorem is vacuous on the very instance the `a = 1` band identity was closed at, and the
propagation has to be restated: `HJO.Mellit.exists_layerWord_shiftAux_of_sorted` is the restatement,
which asks nothing of the widths at all. What the induction really needs at a type-`A` event is
`#{type-A-or-C events of r} ≤ sweepWidth z P`, and here that reads `0 ≤ 0`. -/
@[hjo "lem_sweep_layer_width_refuted"]
theorem not_layerWidth_oneOneOne :
    ¬ (∀ v r : List (ℕ × ℕ), ∀ P : ℕ × ℕ,
        sortByRank 1 1 1 {P ∈ sweptAbove pathOneOne 0 | diagExcess 1 1 P = 1 ∧ P.1 < 1 * 1}
          = v ++ P :: r → r.length + 1 ≤ sweepWidth pathOneOne P) := by
  intro h
  have hlist : sortByRank 1 1 1
      {P ∈ sweptAbove pathOneOne 0 | diagExcess 1 1 P = 1 ∧ P.1 < 1 * 1} = [(0, 1)] := by
    rw [round_pathOneOne, sortByRank_singleton]
  have := h [] [] (0, 1) (by rw [hlist]; rfl)
  rw [sweepWidth_pathOneOne_eq_zero] at this
  omega

end Refutation

end HJO.Mellit

end
