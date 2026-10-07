/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitBEPartner
public meta import HJO.Attr

/-! # The level drop at the origin: rule `B` alone, and the transfer at every point

`HJO.Mellit.eq_dsc_of_recursion_step_of_ne_origin` transfers agreement at one level drop at every
bracketed swept point *but the origin*, the exclusion being forced:
`HJO.Mellit.not_hasBEPartner_origin` shows that the `BE` clause of Mellit's Theorem 4.2 has no
type-`E` premise to be applied to at `(0, 0)`, while
`HJO.Mellit.beClause_unavoidable` shows the origin is a type-`B` event of every above-diagonal path,
so that is the one point where the clause both fires and says nothing. This file closes the origin
and states the transfer with no point excluded.

## The repair

**The missing clause is rule `B` on its own**, with no `u · D(c'')` term:
`HJO.Mellit.dsc_lo_eq_dminus_dsc_hi_origin`. It is not obtained by weakening
`HJO.Mellit.dsc_eq_dminus_add_smul`, and it is not an instance of any earlier clause — the proof of
rule `BE` needs `0 < X` and `0 < Y`, which at the origin fail, and the `A`/`C`/`D` clause needs
`ŷ_X < Y ∨ ŷ_{X+1} = Y`, which at the origin fails too. The proof here is the fibre argument of
`HJO.Mellit.dsc_lo_eq_sweepOperator_dsc_hi` rerun at `(0, 0)`, where three things collapse.

*The `u` term is a sum over the empty set.* By `HJO.Mellit.not_eventType_origin_eq_E` no
above-diagonal path has a type-`E` event at the origin, so the type-`E` class into which
`HJO.Mellit.fibre_split` divides the traces below the level is empty:
`HJO.Mellit.filter_traceIndex_eventType_E_origin_eq_empty`. This is the precise sense in which the
`u` term is *absent* rather than cancelled — nothing is dropped from the identity, and no value of
`u` is excluded.

*The shape of a path at the origin is not a hypothesis but a theorem.* The six local facts that
`HJO.Mellit.colouring_hi_eq_of_colouring_lo_eq` reads — `ŷ_0 ≤ 0`, `0 ≤ ŷ_1`, and the two
equality-with-`Y` tests — hold for *every* above-diagonal path at `(0, 0)`, since `ŷ_0 = 0` and
`ŷ_1 > 0` (`HJO.Mellit.ht_one_pos`). Away from the origin those facts are exactly what the lower
colouring cannot determine, which is why `HJO.Mellit.shape_of_colouring_lo_eq` needs the hypothesis
excluding the types `B` and `E`.

*So the level drop is a bijection of colourings, not merely of traces.*
`HJO.Mellit.colouring_lo_eq_iff_colouring_hi_eq_origin`: two above-diagonal paths share their
colouring below the level at the origin exactly when they share it above. The splice
`HJO.Mellit.raiseFrom`, which the `A`/`C`/`D` argument needs to carry the strictly larger upper
fibre into the lower one, is therefore not needed at all here — the surjectivity step is the
identity map on paths.

## What this does and does not settle

`HJO.Mellit.eq_dsc_of_recursion_step_everywhere` is the transfer at **every** bracketed swept point,
no exclusion. Its hypothesis list is the point: past `HJO.Mellit.SweepRecursionACD` and
`HJO.Mellit.SweepRecursionBE` it carries a third clause,
`HJO.Mellit.SweepRecursionBOrigin`, and that clause is *not* implied by the other two — at the
origin one is inapplicable and the other vacuous. So the repair is not free. It replaces an
unsatisfiable hypothesis by a satisfiable one: `HJO.Mellit.HasBEPartner` at the origin is false for
every path and every level, whereas `HJO.Mellit.SweepRecursionBOrigin` is a determinate one-
predecessor clause that `HJO.Mellit.dsc` satisfies (`HJO.Mellit.dsc_sweepRecursionBOrigin`).

What the braid side owes on Mellit's route is therefore one clause more than Mellit's Theorem
4.2 states, and it is the shape of clause that `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`
already contemplates: a single upper colouring, multiplied by `d_-` at the width of the sweep. Note
also that the origin clause mentions no `u` — the parameter rule `E` contributes does not enter at
the point where rule `E` cannot occur.

Two things are *not* settled here. Iterating the level drops from a level above the rectangle down
to a separating level is the separate obligation
`HJO.Mellit.eq_dsc_of_recursion_step`'s file already names, and nothing here bears on it. And the
origin clause is *not* claimed at any other point: away from the origin the type-`E` class of the
lower fibre is in general nonempty — `HJO.Mellit.hasBEPartner_of_isolates` produces a type-`E`
partner at every other bracketed swept point — so the `u`-free identity is not to be expected there,
and this file does not state it there.

No genericity is spent: `0 < a`, `0 < b`, `0 < N` and nothing else, the same three the origin
results of `HJO.Mellit.not_hasBEPartner_origin` carry. No inverse is introduced —
`HJO.Sweep.dminus` is polynomial in `q` — so unlike rule `C`, whose operator `HJO.Sweep.corner`
carries `(q - 1)⁻¹`, the clause proved here is an identity at every `q` and `u` in a field, with no
excluded value.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {a b N : ℕ}

/-! ### The local shape of an above-diagonal path at the origin -/

/-- **An above-diagonal path is strictly above the origin one column along.** The above-diagonal
condition at `r = 1` reads `b ≤ a ŷ_1`, and `b > 0`, so `ŷ_1 > 0`.

With `ŷ_0 = 0` this is the whole local shape of a path at the origin, and it is the reason the
origin is a type-`B` event of every above-diagonal path (`HJO.Mellit.eventType_origin_eq_B`) and
never a type-`E` one (`HJO.Mellit.not_eventType_origin_eq_E`). -/
theorem ht_one_pos (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {y : Heights a b N}
    (hy : IsAboveDiagonal y) : 0 < ht y 1 := by
  have haN : 0 < a * N := Nat.mul_pos ha hN
  have hd : b * 1 ≤ a * ht y 1 := hy.2.2.2 1 haN
  rcases Nat.eq_zero_or_pos (ht y 1) with h | h
  · rw [h, Nat.mul_zero] at hd; omega
  · exact h

/-- **The `A`/`C`/`D` clause has no instance at the origin.** Its event hypothesis, which
`HJO.Mellit.SweepRecursionACD` states as `ŷ_X < Y ∨ ŷ_{X+1} = Y`, reads `ŷ_0 < 0 ∨ ŷ_1 = 0` at
`(0, 0)`, and both disjuncts fail for every above-diagonal path — the first because heights are
naturals, the second by `HJO.Mellit.ht_one_pos`.

With `HJO.Mellit.not_eventType_origin_eq_E`, which kills the type-`E` premise of
`HJO.Mellit.SweepRecursionBE`, this says that *neither* clause of Mellit's Theorem 4.2 has a single
instance at the origin: one is inapplicable and the other vacuous. That is why
`HJO.Mellit.SweepRecursionBOrigin` is a genuine third hypothesis rather than a consequence of the
first two. -/
theorem not_ht_lt_or_ht_succ_eq_origin (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {y : Heights a b N} (hy : IsAboveDiagonal y) : ¬ (ht y 0 < 0 ∨ ht y (0 + 1) = 0) := by
  have p1 : 0 < ht y (0 + 1) := by simpa using ht_one_pos ha hb hN hy
  omega

/-- **At the origin the level drop is a bijection of colourings.** Two above-diagonal paths have the
same colouring below the level exactly when they have the same colouring above it.

This is the structural fact that makes the origin a one-predecessor step. Both directions are
`HJO.Mellit.colouring_hi_eq_of_colouring_lo_eq` and
`HJO.Mellit.colouring_lo_eq_of_colouring_hi_eq`, whose six local hypotheses — the path weakly under
the point on the left, weakly over it on the right, and the two equality tests agreeing between the
paths — are *unconditional* at `(0, 0)`: `ŷ_0 = 0` makes the left tests true for both paths and
`HJO.Mellit.ht_one_pos` makes the right tests false for both. Away from the origin they are exactly
what the lower colouring fails to record, which is why
`HJO.Mellit.shape_of_colouring_lo_eq` must exclude the types `B` and `E`. -/
theorem colouring_lo_eq_iff_colouring_hi_eq_origin (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {ηlo ηhi : ℚ} (hI : Isolates a b N 0 0 ηlo ηhi) {y₁ y₂ : Heights a b N}
    (hy₁ : IsAboveDiagonal y₁) (hy₂ : IsAboveDiagonal y₂) :
    colouring y₁ ηlo = colouring y₂ ηlo ↔ colouring y₁ ηhi = colouring y₂ ηhi := by
  have e1 : ht y₁ 0 = 0 := hy₁.1
  have e2 : ht y₂ 0 = 0 := hy₂.1
  have p1 : 0 < ht y₁ (0 + 1) := by simpa using ht_one_pos ha hb hN hy₁
  have p2 : 0 < ht y₂ (0 + 1) := by simpa using ht_one_pos ha hb hN hy₂
  exact ⟨colouring_hi_eq_of_colouring_lo_eq ha hb hN hI (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega),
    colouring_lo_eq_of_colouring_hi_eq ha hb hN hI (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)⟩

/-- **What a path with the reference path's colouring at the lower level has in common with it, at
the origin.** The analogue of `HJO.Mellit.key_of_colouring_lo_eq`, which is unavailable here because
its hypothesis `ŷ_X < Y ∨ ŷ_{X+1} = Y` fails at the origin for every above-diagonal path. Every
clause is cheaper than in the general case: the origin is swept by every path
(`HJO.Mellit.mem_sweptRegion_origin`), the event there is of type `B` for every path
(`HJO.Mellit.eventType_origin_eq_B`) so the two event types agree without argument, and the upper
colourings agree by `HJO.Mellit.colouring_lo_eq_iff_colouring_hi_eq_origin`. -/
theorem key_of_colouring_lo_eq_origin (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {ηlo ηhi : ℚ} (hI : Isolates a b N 0 0 ηlo ηhi) {ŷ y : Heights a b N}
    (hŷ : IsAboveDiagonal ŷ) (hy : IsAboveDiagonal y)
    (hcl : colouring y ηlo = colouring ŷ ηlo) :
    ((0 : ℕ), (0 : ℕ)) ∈ sweptRegion y ∧ colouring y ηhi = colouring ŷ ηhi ∧
      eventType y ((0 : ℕ), (0 : ℕ)) = eventType ŷ ((0 : ℕ), (0 : ℕ)) ∧
      sweepRight y ((0 : ℕ), (0 : ℕ)) = sweepRight ŷ ((0 : ℕ), (0 : ℕ)) ∧
      sweepOperator q u y ((0 : ℕ), (0 : ℕ)) = sweepOperator q u ŷ ((0 : ℕ), (0 : ℕ)) := by
  have hcol : colouring y ηhi = colouring ŷ ηhi :=
    (colouring_lo_eq_iff_colouring_hi_eq_origin ha hb hN hI hy hŷ).1 hcl
  have hev : eventType y ((0 : ℕ), (0 : ℕ)) = eventType ŷ ((0 : ℕ), (0 : ℕ)) := by
    rw [eventType_origin_eq_B ha hb hN hy, eventType_origin_eq_B ha hb hN hŷ]
  have hn : colouringNorth y ηhi = colouringNorth ŷ ηhi := by
    rw [← filter_colouring_lt, ← filter_colouring_lt, hcol]
  refine ⟨mem_sweptRegion_origin, hcol, hev, ?_,
    sweepOperator_eq_of_colouring_hi_eq q u hI hcol hev⟩
  rw [sweepRight, sweepRight, liveSteps_eq_colouringNorth hI, liveSteps_eq_colouringNorth hI, hn]

/-! ### The type-`E` class of the fibre at the origin is empty -/

/-- **At the origin no trace below the level carries a type-`E` event.** The traces of
`HJO.Mellit.traceIndex` are realized by above-diagonal paths, a triple of a trace records the event
type at its point (`HJO.Mellit.Isolated.eq_of_mem_levelTrace`), and
`HJO.Mellit.not_eventType_origin_eq_E` forbids a type-`E` event at `(0, 0)`.

This is where the `u` term of rule `BE` goes. In the proof of
`HJO.Mellit.dsc_eq_dminus_add_smul` the traces below the level split into the class carrying
`((0,0), B, r)` and the class carrying `((0,0), E, r)`, the second contributing `u` times the
invariant of the type-`E` upper colouring; at the origin that class is empty, so the sum over it is
`0` and the identity has no `u` term. The term is absent, not cancelled: no relation on `u` is used
and no value of `u` is excluded. -/
theorem filter_traceIndex_eventType_E_origin_eq_empty (ηlo : ℚ) (c : Finset (ℕ × ℕ)) (r : ℕ) :
    {τ ∈ traceIndex a b N ηlo c | (((0 : ℕ), (0 : ℕ)), EventType.E, r) ∈ τ} = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.2 fun τ hτ => ?_
  obtain ⟨hτT, hmem⟩ := Finset.mem_filter.1 hτ
  obtain ⟨y, hy, -, hty⟩ := mem_traceIndex_iff.1 hτT
  rw [← hty] at hmem
  exact not_eventType_origin_eq_E hy (Isolated.eq_of_mem_levelTrace hmem).1

/-! ### The level drop at the origin -/

/-- **Lowering the level past the origin multiplies the invariant by the event's own operator.** The
fibre argument of `HJO.Mellit.dsc_lo_eq_sweepOperator_dsc_hi` rerun at `(0, 0)`, where that theorem
does not apply: its hypothesis `ŷ_X < Y ∨ ŷ_{X+1} = Y` is false at the origin for every
above-diagonal path, the origin being a type-`B` event.

The correspondence of traces is the same erasure of the point's own triple, but the surjectivity
step is the *identity* on paths rather than the splice `HJO.Mellit.raiseFrom`: at the origin the
upper fibre is not larger than the lower one, by
`HJO.Mellit.colouring_lo_eq_iff_colouring_hi_eq_origin`. -/
theorem dsc_lo_eq_sweepOperator_dsc_hi_origin (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {ηlo ηhi : ℚ} (hI : Isolates a b N 0 0 ηlo ηhi) {ŷ : Heights a b N}
    (hŷ : IsAboveDiagonal ŷ) :
    dsc q u a b N ηlo (colouring ŷ ηlo) =
      sweepOperator q u ŷ ((0 : ℕ), (0 : ℕ)) (dsc q u a b N ηhi (colouring ŷ ηhi)) := by
  obtain ⟨x₀, hx₀⟩ : ∃ x : (ℕ × ℕ) × EventType × ℕ,
      x = (((0 : ℕ), (0 : ℕ)) , eventType ŷ ((0 : ℕ), (0 : ℕ)),
        sweepRight ŷ ((0 : ℕ), (0 : ℕ))) := ⟨_, rfl⟩
  have hx₀not : ∀ y : Heights a b N, x₀ ∉ levelTrace y ηhi := by
    intro y
    rw [hx₀]
    exact notMem_levelTrace_hi hI y _ _
  have hins : ∀ y : Heights a b N, IsAboveDiagonal y → colouring y ηlo = colouring ŷ ηlo →
      levelTrace y ηlo = insert x₀ (levelTrace y ηhi) := by
    intro y hy hcl
    obtain ⟨hsw, -, hev, hr, -⟩ := key_of_colouring_lo_eq_origin q u ha hb hN hI hŷ hy hcl
    have h := levelTrace_lo_eq_insert_triple ha hI hsw
    rwa [hev, hr, ← hx₀] at h
  have hlo : ∀ τ ∈ traceIndex a b N ηlo (colouring ŷ ηlo),
      IsAboveDiagonal (traceRep a b N ηlo (colouring ŷ ηlo) τ) ∧
        colouring (traceRep a b N ηlo (colouring ŷ ηlo) τ) ηhi = colouring ŷ ηhi ∧
        levelTrace (traceRep a b N ηlo (colouring ŷ ηlo) τ) ηhi = τ.erase x₀ ∧ x₀ ∈ τ ∧
        partialSweepWord q u (traceRep a b N ηlo (colouring ŷ ηlo) τ) ηlo =
          sweepOperator q u ŷ ((0 : ℕ), (0 : ℕ)) *
            partialSweepWord q u (traceRep a b N ηlo (colouring ŷ ηlo) τ) ηhi := by
    intro τ hτ
    obtain ⟨hy, hcl, htr⟩ := traceRep_spec hτ
    obtain ⟨hsw, hcol, -, -, hop⟩ := key_of_colouring_lo_eq_origin q u ha hb hN hI hŷ hy hcl
    have h := hins _ hy hcl
    refine ⟨hy, hcol, ?_, ?_, ?_⟩
    · exact ((congrArg (fun s => Finset.erase s x₀) (htr.symm.trans h)).trans
        (Finset.erase_insert (hx₀not _))).symm
    · rw [← htr, h]
      exact Finset.mem_insert_self _ _
    · rw [partialSweepWord_eq_sweepOperator_mul q u ha hI.hi hI.ltP hI.Plt hI.iso hsw, hop]
  have hmapsto : ∀ τ ∈ traceIndex a b N ηlo (colouring ŷ ηlo),
      τ.erase x₀ ∈ traceIndex a b N ηhi (colouring ŷ ηhi) := by
    intro τ hτ
    obtain ⟨hy, hcol, h1, -, -⟩ := hlo τ hτ
    rw [← h1]
    exact mem_traceIndex_of_colouring_eq _ hy ηhi hcol
  rw [dsc, dsc, map_sum]
  refine Finset.sum_nbij' (fun τ => τ.erase x₀) (fun σ => insert x₀ σ) hmapsto ?_ ?_ ?_ ?_
  · intro σ hσ
    obtain ⟨y', hy', hcol', htr'⟩ := exists_path_of_mem_traceIndex hσ
    have hcl : colouring y' ηlo = colouring ŷ ηlo :=
      (colouring_lo_eq_iff_colouring_hi_eq_origin ha hb hN hI hy' hŷ).2 hcol'
    rw [← htr', ← hins _ hy' hcl]
    exact mem_traceIndex_of_colouring_eq _ hy' ηlo hcl
  · intro τ hτ
    obtain ⟨-, -, -, h2, -⟩ := hlo τ hτ
    exact Finset.insert_erase h2
  · intro σ hσ
    obtain ⟨y', hy', hcol', htr'⟩ := exists_path_of_mem_traceIndex hσ
    rw [← htr']
    exact Finset.erase_insert (hx₀not y')
  · intro τ hτ
    obtain ⟨hy, hcol, h1, h2, h3⟩ := hlo τ hτ
    obtain ⟨hz1, hz2, hz3⟩ := traceRep_spec (hmapsto τ hτ)
    rw [h3, Module.End.mul_apply,
      partialSweepWord_eq_of_levelTrace_eq q u ha hN hy hz1 (by rw [h1, hz3])]

/-- **Rule `B` alone at the origin: the level recursion at `(0, 0)`.** With `ηlo < rk̂(0,0) < ηhi`
isolating the rank of the origin and `ŷ` any above-diagonal `(aN, bN)`-path,
`D_{ηlo, c_{ηlo}(ŷ)} = d_- D_{ηhi, c_{ηhi}(ŷ)}`,
the lowering operator read at the width of the sweep at the origin, the way
`HJO.Mellit.sweepOperator` reads it.

This is the clause Mellit's Theorem 4.2 lacks. His rule `BE` at this point asserts `c` is obtained
in `2` ways and relates the lower value to *two* upper values; by
`HJO.Mellit.not_eventType_origin_eq_E` the second way does not exist at the origin, so
`HJO.Mellit.dsc_eq_dminus_add_smul` is vacuous there
(`HJO.Mellit.not_hasBEPartner_origin`) and the recursion determines nothing. The statement above is
what is true instead: the same identity with the `u` term deleted, and it is *not* the `BE` rule
weakened — the missing term is a sum over the empty set
(`HJO.Mellit.filter_traceIndex_eventType_E_origin_eq_empty`), not a term made to vanish by a
condition on `q` or `u`.

It is also not an instance of `HJO.Mellit.dsc_lo_eq_sweepOperator_dsc_hi`, whose hypothesis excludes
the types `B` and `E`, nor of rules `A`, `C`, `D`, whose event types do not occur at the origin.
`0 < a`, `0 < b` and `0 < N` are all it costs; no inverse is introduced, `HJO.Sweep.dminus` being
polynomial in `q`, so there is no excluded value of `q` or `u`. -/
@[hjo "lem_mellit_thm42_origin"]
theorem dsc_lo_eq_dminus_dsc_hi_origin (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {ηlo ηhi : ℚ} (hI : Isolates a b N 0 0 ηlo ηhi) {ŷ : Heights a b N}
    (hŷ : IsAboveDiagonal ŷ) :
    dsc q u a b N ηlo (colouring ŷ ηlo) =
      dminus q (sweepWidth ŷ ((0 : ℕ), (0 : ℕ))) (dsc q u a b N ηhi (colouring ŷ ηhi)) := by
  rw [dsc_lo_eq_sweepOperator_dsc_hi_origin q u ha hb hN hI hŷ,
    sweepOperator_of_eventType_B ŷ (eventType_origin_eq_B ha hb hN hŷ)]

/-- **The origin clause is not vacuous, and in range.** On the `2 × 3` rectangle — coprime with
`1 < a < b` — the above-diagonal path `(0, 2, 3)` and a bracketing pair of admissible levels at the
origin, which `HJO.Mellit.exists_isolates` produces at every lattice point of the rectangle, satisfy
every hypothesis of `HJO.Mellit.dsc_lo_eq_dminus_dsc_hi_origin` at once. So the identity is a
statement about a configuration that occurs, which is the check
`HJO.Mellit.dsc_eq_dminus_add_smul_example` performs for rule `BE` and which rule `BE` at the origin
would fail: there it is the type-`E` path that cannot be produced. -/
theorem dsc_lo_eq_dminus_dsc_hi_origin_example (q u : L) :
    ∃ ηlo ηhi : ℚ, ηlo < ηhi ∧
      dsc q u 2 3 1 ηlo (colouring (![0, 2, 3] : Heights 2 3 1) ηlo)
        = dminus q (sweepWidth (![0, 2, 3] : Heights 2 3 1) ((0 : ℕ), (0 : ℕ)))
            (dsc q u 2 3 1 ηhi (colouring (![0, 2, 3] : Heights 2 3 1) ηhi)) := by
  obtain ⟨ηlo, ηhi, hI⟩ := exists_isolates 2 3 1 0 0 (by norm_num) (by norm_num)
  exact ⟨ηlo, ηhi, hI.ltP.trans hI.Plt,
    dsc_lo_eq_dminus_dsc_hi_origin q u (by norm_num) (by norm_num) (by norm_num) hI (by decide)⟩

/-! ### The origin clause as a property of a candidate, and the transfer -/

/-- **The origin clause of the level recursion, asked of a candidate `R`.** Verbatim the shape of
`HJO.Mellit.dsc_lo_eq_dminus_dsc_hi_origin`, which is the proved statement for `R = dsc`.

This is a third clause, beside `HJO.Mellit.SweepRecursionACD` and
`HJO.Mellit.SweepRecursionBE`, and it is not implied by them: at the origin the first is
inapplicable, the event there being of type `B` for every above-diagonal path
(`HJO.Mellit.eventType_origin_eq_B`), and the second is vacuous, its type-`E` premise being
unsatisfiable (`HJO.Mellit.not_eventType_origin_eq_E`). Unlike `HJO.Mellit.HasBEPartner`, which at
the origin is *false*, this clause is a determinate one-predecessor recursion step: one upper
colouring, one operator.

Note that it does not mention `u`. The parameter rule `E` contributes does not enter at the one
point where rule `E` cannot occur. -/
def SweepRecursionBOrigin (q : L) (a b N : ℕ) (R : ℚ → Finset (ℕ × ℕ) → Total L) : Prop :=
  ∀ ηlo ηhi : ℚ, Isolates a b N 0 0 ηlo ηhi → ∀ y : Heights a b N, IsAboveDiagonal y →
    R ηlo (colouring y ηlo)
      = dminus q (sweepWidth y ((0 : ℕ), (0 : ℕ))) (R ηhi (colouring y ηhi))

/-- **`HJO.Mellit.dsc` satisfies the origin clause**, which is
`HJO.Mellit.dsc_lo_eq_dminus_dsc_hi_origin` packaged as
`HJO.Mellit.SweepRecursionBOrigin`. Recorded so the abstraction is known to be inhabited: a
recursion property with no example is a hypothesis nothing satisfies, and the transfer below would
then be vacuous in exactly the way `HJO.Mellit.eq_dsc_of_recursion_step` is at the origin. -/
theorem dsc_sweepRecursionBOrigin (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    SweepRecursionBOrigin q a b N (dsc q u a b N) :=
  fun _ _ hI _ hy => dsc_lo_eq_dminus_dsc_hi_origin q u ha hb hN hI hy

/-- **One drop of the level transfers agreement at the origin.** The counterpart of
`HJO.Mellit.eq_dsc_of_recursion_step_acd` at the one point that theorem cannot reach, using the
origin clause in place of the `A`/`C`/`D` one. Nothing is owed beyond that clause: the origin step
has one predecessor, so a single path's upper value suffices and no partner is needed. -/
theorem eq_dsc_of_recursion_step_origin (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {R : ℚ → Finset (ℕ × ℕ) → Total L} (hB0 : SweepRecursionBOrigin q a b N R)
    {ηlo ηhi : ℚ} (hI : Isolates a b N 0 0 ηlo ηhi) {y : Heights a b N}
    (hy : IsAboveDiagonal y)
    (hhi : R ηhi (colouring y ηhi) = dsc q u a b N ηhi (colouring y ηhi)) :
    R ηlo (colouring y ηlo) = dsc q u a b N ηlo (colouring y ηlo) := by
  rw [hB0 ηlo ηhi hI y hy, hhi, dsc_lo_eq_dminus_dsc_hi_origin q u ha hb hN hI hy]

/-- **One drop of the level transfers agreement at every bracketed swept point, with no point
excluded and no partner hypothesis.** Mellit's closing sentence for his Theorem 5.8 at one level
drop, as far as one level drop goes: a candidate `R` satisfying the two clauses of his Theorem 4.2
*and the origin clause* and agreeing with `HJO.Mellit.dsc` at the upper level on every
above-diagonal path's colouring agrees with it at the lower level, at every bracketed point of the
rectangle the path sweeps.

`HJO.Mellit.eq_dsc_of_recursion_step_of_ne_origin` supplies every point but the origin, with
`HJO.Mellit.HasBEPartner` discharged by `HJO.Mellit.hasBEPartner_of_isolates`, and
`HJO.Mellit.eq_dsc_of_recursion_step_origin` supplies the origin.

The third clause is the price, and it is exact. `HJO.Mellit.eq_dsc_of_recursion_step` carries
instead the hypothesis `HJO.Mellit.HasBEPartner`, which at the origin is false for every path, every
level and all `a`, `b`, `N` — so that theorem cannot be applied there at all, while
`HJO.Mellit.beClause_unavoidable` shows the origin is where its `BE` case is forced. Replacing it by
a clause `HJO.Mellit.dsc` provably satisfies is what closes the point. -/
theorem eq_dsc_of_recursion_step_everywhere (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {R : ℚ → Finset (ℕ × ℕ) → Total L} (hACD : SweepRecursionACD q u a b N R)
    (hBE : SweepRecursionBE q u a b N R) (hB0 : SweepRecursionBOrigin q a b N R) {X Y : ℕ}
    {ηlo ηhi : ℚ} (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hPsw : (X, Y) ∈ sweptRegion y)
    (hhi : ∀ z : Heights a b N, IsAboveDiagonal z →
      R ηhi (colouring z ηhi) = dsc q u a b N ηhi (colouring z ηhi)) :
    R ηlo (colouring y ηlo) = dsc q u a b N ηlo (colouring y ηlo) := by
  by_cases horig : (X, Y) = ((0 : ℕ), (0 : ℕ))
  · obtain ⟨hX, hY⟩ := Prod.mk.injEq .. ▸ horig
    subst hX
    subst hY
    exact eq_dsc_of_recursion_step_origin q u ha hb hN hB0 hI hy (hhi y hy)
  · exact eq_dsc_of_recursion_step_of_ne_origin q u ha hb hN hACD hBE hI hy hPsw horig hhi

end HJO.Mellit

end
