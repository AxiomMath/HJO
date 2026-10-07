/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitUnsweptDrop
public import HJO.Shuffle.ColouringInitial

/-! # Iterating the level drop: the induction principle behind Mellit's Theorem 5.8

Mellit proves his Theorem 5.8 (`HJO.Mellit.braidValueColouring_eq_dsc_floor`) in one sentence —
"both sides of the statement satisfy the same recursions and the same initial conditions, so the
proof is complete". The one level drop is `HJO.Mellit.eq_dsc_of_recursion_step_any`; this file
performs the induction, and `HJO.Mellit.eq_dsc_of_recursions` is the result: **a candidate `R`
satisfying the recursion clauses at every level drop and the initial condition agrees with
`HJO.Mellit.dsc` at every admissible colouring of every admissible level.**

## The induction, and the chain of levels it walks

The measure is `HJO.Mellit.ranksAbove a b N η`, the lattice points of the rectangle whose rank
outranks the level. Above every rank it is empty, and that is the base case: there every colouring
of every above-diagonal path is empty (`HJO.Mellit.colouring_eq_empty_of_forall_lt`) and the
invariant is `1` (`HJO.Mellit.dsc_eq_one_of_forall_lt`), so the initial condition settles the
level.

For the step, the levels are not chosen in advance: at a level `η` with something still above it,
`Finset.exists_min_image` takes the *least* rank `r` above `η` and the upper level is `r + 1/2`.
That pair brackets the point carrying `r` — nothing of the rectangle can sit between `η` and
`r + 1/2` except `r` itself, by minimality and because ranks are integers — so `HJO.Mellit.Isolates`
holds, and the measure drops, that point having left it. Iterating from the top of the rectangle
down, the chain therefore crosses the rank of **every** lattice point of the rectangle, one at a
time, and that is why the unswept clause is needed: the crossed point is in general not swept by the
path whose colouring is being computed.

The base case is stated at a weaker hypothesis than
`HJO.Mellit.isAdmissibleColouring_empty_and_dsc_eq_one`, which asks the level to be above every
rank *plus the attack window*. Above every rank alone is enough, and the induction needs it to be:
the chain it walks stops as soon as the ranks are exhausted, and `rk̂ + ω` is the rank of a point
one row higher, which for a point on the top edge of the rectangle is outside it. The two halves of
the weaker statement are `HJO.Mellit.colouring_eq_empty_of_forall_lt` and
`HJO.Mellit.dsc_eq_one_of_forall_lt`; the second is the first with the trace and the partial word
added, which above every rank are the empty set and the identity.

## What this settles, and what it does not

It settles the induction, in the precise sense that the *five* hypotheses it carries are what the
right-hand side of Theorem 5.8 has to be shown to satisfy. Four are recursion clauses —
`HJO.Mellit.SweepRecursionACD`, `HJO.Mellit.SweepRecursionBE`,
`HJO.Mellit.SweepRecursionBOrigin`, `HJO.Mellit.SweepRecursionUnswept` — and the fifth is
`HJO.Mellit.SweepInitialCondition`. Mellit's Theorem 4.2 states the first two; the third and fourth
are the clauses supplied in `HJO/Shuffle/MellitOriginTransfer.lean` and
`HJO/Shuffle/MellitUnsweptDrop.lean` for the two drops Theorem 4.2 does not cover, at the origin and
at a crossed point the path does not sweep. All five are inhabited by
`HJO.Mellit.dsc` itself, so the principle is not a statement about an empty class of candidates.

**It does not by itself prove `HJO.Mellit.braidValueColouring_eq_dsc_floor`.** The braid side of
that statement — `q^{(inv_fin - inv_ini)/2} π_k(B_{s,c}) d_+^k(1)` — is a perfectly writable
candidate `R`, but that it satisfies the recursion clauses is a separate theorem,
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor`, and it does so only above the floor `aN`; the
iteration in that form is `HJO.Mellit.agreesWithDsc_of_recursions_floor`
(`HJO/Shuffle/MellitThm58Floor.lean`). So what is proved here is the *implication*: with it, the
iteration is no longer the missing step.

The agreement is at *every* admissible level, so in particular at a separating one —
`HJO.Mellit.eq_dsc_sepLevel` records that at `HJO.Mellit.sepLevel a N`, which
`HJO.Mellit.isAdmissibleLevel_sepLevel` says is admissible. That is the level at which
`HJO.Mellit.braidValueColouring_eq_dsc_floor` is used, and it is not an extra obligation: the
induction passes through the separating levels like any others.

No genericity is spent here. Every inverse in the definitions sits inside the clauses carried as
hypotheses on `R` — the `(q - 1)⁻¹` of `HJO.Sweep.corner` inside `HJO.Mellit.SweepRecursionACD`,
the `(q u)⁻¹` of `HJO.Sweep.zop` likewise — and nothing below evaluates one, so the theorems hold at
every `q` and `u` in a field, with `0 < a`, `0 < b`, `0 < N` the only arithmetic hypotheses. The
coprimality `1 < a < b` of the range is not needed and not assumed.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {a b N : ℕ}

/-! ### The initial condition above every rank -/

/-- **The level is above every rank of the rectangle.** The hypothesis of the base case of the level
induction, and the range of levels at which the initial condition of Mellit's closing sentence is
asked. It is weaker than the condition `rk̂(P) + ω < η` of
`HJO.Mellit.isAdmissibleColouring_empty_and_dsc_eq_one`, which is why
`HJO.Mellit.colouring_eq_empty_of_forall_lt` and `HJO.Mellit.dsc_eq_one_of_forall_lt` are proved
here rather than read off `HJO.Mellit.isAdmissibleColouring_empty_and_dsc_eq_one`. -/
def AboveEveryRank (a b N : ℕ) (η : ℚ) : Prop :=
  ∀ Q : ℕ × ℕ, Q.1 ≤ a * N → Q.2 ≤ b * N → ((pointRank a b N Q : ℤ) : ℚ) < η

/-- **Above every rank of the rectangle every colouring is empty.** A north step is crossed only
below the rank of its head, which is the rank of a lattice point of the rectangle by
`HJO.Paths.abovePointRank_succ`, and an east step only below its own rank; both are refuted.

This is the hypothesis of `HJO.Mellit.isAdmissibleColouring_empty_and_dsc_eq_one` weakened from
`rk̂(P) + ω < η` to `rk̂(P) < η`, which is what the level induction can supply: the chain of drops
stops when the ranks of the rectangle are exhausted, and `rk̂(P) + ω` is the rank of a point one row
above `P`, outside the rectangle when `P` is on its top edge. -/
theorem colouring_eq_empty_of_forall_lt {η : ℚ} (hη : AboveEveryRank a b N η)
    (y : Heights a b N) : colouring y η = ∅ := by
  rw [colouring, Finset.union_eq_empty]
  refine ⟨Finset.filter_eq_empty_iff.2 fun {P} hP => ?_,
    Finset.filter_eq_empty_iff.2 fun {P} hP => ?_⟩
  · obtain ⟨h1, -, h3⟩ := mem_northSteps_iff.1 hP
    have hub : P.2 + 1 ≤ b * N := by
      have := ht_le_mul y (P.1 + 1)
      omega
    have hsucc : pointRank a b N (P.1, P.2 + 1) =
        pointRank a b N P + (attackWindow a N : ℤ) := abovePointRank_succ a b N P.1 P.2
    have hcast : ((pointRank a b N (P.1, P.2 + 1) : ℤ) : ℚ) =
        ((pointRank a b N P : ℤ) : ℚ) + ((attackWindow a N : ℕ) : ℚ) := by
      rw [hsucc]; push_cast; ring
    have hlt := hη (P.1, P.2 + 1) (by omega) hub
    rw [hcast] at hlt
    rintro ⟨-, h⟩
    exact absurd h (not_lt.2 hlt.le)
  · obtain ⟨h1, h2⟩ := mem_eastSteps_iff.1 hP
    have h3 : P.2 ≤ b * N := h2 ▸ ht_le_mul y _
    rintro ⟨-, h⟩
    exact absurd h (not_lt.2 (hη P (by omega) h3).le)

/-- **Above every rank of the rectangle the invariant of the empty colouring is `1`.** Nothing is
swept above the level, so every trace is empty and every partial sweep word is the identity, and the
index set of `HJO.Mellit.dsc` is the single trace `∅` — single, and not empty, because
`HJO.Mellit.maxAbovePath` realises it.

This is `HJO.Mellit.isAdmissibleColouring_empty_and_dsc_eq_one` at the weaker hypothesis discussed
at `HJO.Mellit.colouring_eq_empty_of_forall_lt`. `0 < a` is spent for the same reason it is there:
at `a = 0 < b` no above-diagonal path exists and the sum is empty. -/
theorem dsc_eq_one_of_forall_lt (q u : L) (ha : 0 < a) {η : ℚ}
    (hη : AboveEveryRank a b N η) :
    dsc q u a b N η (∅ : Finset (ℕ × ℕ)) = (1 : Total L) := by
  have hcol : ∀ y : Heights a b N, colouring y η = ∅ := colouring_eq_empty_of_forall_lt hη
  have hswept : ∀ y : Heights a b N, sweptAbove y η = ∅ := by
    intro y
    refine Finset.filter_eq_empty_iff.2 fun {P} hP => ?_
    obtain ⟨h1, -, h3⟩ := Paths.mem_sweptRegion.1 hP
    exact not_lt.2 (hη P h1 (h3.trans (ht_le_mul y _))).le
  have htrace : ∀ y : Heights a b N, levelTrace y η = ∅ := fun y => by
    rw [levelTrace, hswept, Finset.image_empty]
  have hword : ∀ y : Heights a b N, partialSweepWord q u y η = (1 : Module.End L (Total L)) :=
    fun y => by rw [partialSweepWord, hswept, sortByRank_empty, List.map_nil, List.prod_nil]
  have hindex : traceIndex a b N η (∅ : Finset (ℕ × ℕ)) = {∅} := by
    refine Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_image.2
      ⟨maxAbovePath a b N, Finset.mem_filter.2 ⟨Finset.mem_univ _,
        isAboveDiagonal_maxAbovePath ha, hcol _⟩, htrace _⟩, fun τ hτ => ?_⟩
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hτ
    exact htrace y
  rw [dsc, hindex, Finset.sum_singleton, hword]
  rfl

/-! ### The two properties of a candidate the induction reads -/

/-- **Agreement of a candidate with `HJO.Mellit.dsc` at one level**, on the colouring of every
above-diagonal path — equivalently, at every admissible colouring at that level, since
`HJO.Mellit.IsAdmissibleColouring` is the bare existential. This is what the induction carries. -/
def AgreesWithDsc (q u : L) (a b N : ℕ) (R : ℚ → Finset (ℕ × ℕ) → Total L)
    (η : ℚ) : Prop :=
  ∀ y : Heights a b N, IsAboveDiagonal y →
    R η (colouring y η) = dsc q u a b N η (colouring y η)

/-- **The initial condition of Mellit's closing sentence, asked of a candidate `R`.** Verbatim the
shape of `HJO.Mellit.dsc_eq_one_of_forall_lt`, which is this statement for `R = dsc`: above
every rank of the rectangle the value at the empty colouring is the vacuum `1`.

The level is asked to be admissible, which costs nothing — the induction only ever visits admissible
levels — and the bound is `rk̂(Q) < η` rather than `rk̂(Q) + ω < η`, which is what
makes the condition usable as the base case. -/
def SweepInitialCondition (a b N : ℕ) (R : ℚ → Finset (ℕ × ℕ) → Total L) : Prop :=
  ∀ η : ℚ, IsAdmissibleLevel η → AboveEveryRank a b N η →
    R η (∅ : Finset (ℕ × ℕ)) = (1 : Total L)

/-- **`HJO.Mellit.dsc` satisfies the initial condition**, which is
`HJO.Mellit.dsc_eq_one_of_forall_lt` packaged as `HJO.Mellit.SweepInitialCondition`. With the four
recursion clauses this makes every hypothesis of the induction inhabited. -/
theorem dsc_sweepInitialCondition (q u : L) (ha : 0 < a) :
    SweepInitialCondition a b N (dsc q u a b N) :=
  fun _ _ hη => dsc_eq_one_of_forall_lt q u ha hη

/-! ### The measure of the induction -/

/-- The lattice points of the rectangle that outrank the level: the measure of the level induction.
It is empty above every rank of the rectangle, and grows by exactly one point at each drop the chain
of `HJO.Mellit.Isolates` performs. -/
def ranksAbove (a b N : ℕ) (η : ℚ) : Finset (ℕ × ℕ) :=
  {Q ∈ Finset.Iic (a * N) ×ˢ Finset.Iic (b * N) | η < ((pointRank a b N Q : ℤ) : ℚ)}

theorem mem_ranksAbove {η : ℚ} {Q : ℕ × ℕ} :
    Q ∈ ranksAbove a b N η ↔
      Q.1 ≤ a * N ∧ Q.2 ≤ b * N ∧ η < ((pointRank a b N Q : ℤ) : ℚ) := by
  simp only [ranksAbove, Finset.mem_filter, Finset.mem_product, Finset.mem_Iic, and_assoc]

/-- **The base case.** With no rank of the rectangle above the level, every colouring is empty and
its invariant is `1`, so the initial condition alone settles the level. Admissibility is what turns
"no rank strictly above" into "every rank strictly below": a rank equal to the level is impossible
by `HJO.Mellit.cast_pointRank_ne_of_isAdmissibleLevel`. -/
theorem agreesWithDsc_of_ranksAbove_eq_empty (q u : L) (ha : 0 < a)
    {R : ℚ → Finset (ℕ × ℕ) → Total L} (hinit : SweepInitialCondition a b N R) {η : ℚ}
    (hη : IsAdmissibleLevel η) (h : ranksAbove a b N η = ∅) :
    AgreesWithDsc q u a b N R η := by
  have hlt : AboveEveryRank a b N η := by
    intro Q h1 h2
    have hne := cast_pointRank_ne_of_isAdmissibleLevel hη a b N Q
    rcases lt_trichotomy ((pointRank a b N Q : ℤ) : ℚ) η with h3 | h3 | h3
    · exact h3
    · exact absurd h3 hne
    · exact absurd (Finset.eq_empty_iff_forall_notMem.1 h Q (mem_ranksAbove.2 ⟨h1, h2, h3⟩))
        (by simp)
  intro y hy
  rw [colouring_eq_empty_of_forall_lt hlt y, hinit η hη hlt, dsc_eq_one_of_forall_lt q u ha hlt]

/-! ### The iteration -/

/-- **The iteration principle behind Mellit's Theorem 5.8.** A candidate `R` satisfying the four
clauses of the level recursion and the initial condition agrees with `HJO.Mellit.dsc` at every
admissible level.

The proof is the induction on `HJO.Mellit.ranksAbove` described in the module docstring: at a level
with a rank still above it, `Finset.exists_min_image` picks the least such rank, half a unit above
it is the next level up, that pair satisfies `HJO.Mellit.Isolates` at the point carrying the rank,
and the measure has dropped by at least that point. The drop itself is
`HJO.Mellit.eq_dsc_of_recursion_step_any`, which needs all four clauses — the point the chain
crosses is in general not swept by the path in hand, and then only the unswept clause speaks. -/
theorem agreesWithDsc_of_recursions (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {R : ℚ → Finset (ℕ × ℕ) → Total L} (hACD : SweepRecursionACD q u a b N R)
    (hBE : SweepRecursionBE q u a b N R) (hB0 : SweepRecursionBOrigin q a b N R)
    (hUn : SweepRecursionUnswept a b N R) (hinit : SweepInitialCondition a b N R)
    {η : ℚ} (hη : IsAdmissibleLevel η) : AgreesWithDsc q u a b N R η := by
  suffices H : ∀ n : ℕ, ∀ η : ℚ, IsAdmissibleLevel η → #(ranksAbove a b N η) ≤ n →
      AgreesWithDsc q u a b N R η from H _ η hη le_rfl
  intro n
  induction n with
  | zero =>
    intro η hη hcard
    exact agreesWithDsc_of_ranksAbove_eq_empty q u ha hinit hη
      (Finset.card_eq_zero.1 (Nat.le_zero.1 hcard))
  | succ n ih =>
    intro η hη hcard
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
      have hlt := Finset.card_lt_card
        (LE.le.ssubset_of_mem_notMem hsub hP hnot)
      omega
    intro y hy
    exact eq_dsc_of_recursion_step_any q u ha hb hN hACD hBE hB0 hUn hI hy (ih _ hIhi hcard')

/-- **The iteration principle at an admissible colouring**, which is the shape Mellit's Theorem 5.8
is stated in: a candidate satisfying the four recursion clauses and the initial condition has the
same value as `HJO.Mellit.dsc` at every admissible colouring of every admissible level.

`HJO.Mellit.IsAdmissibleColouring` is the existence of an above-diagonal path with that colouring,
so this is `HJO.Mellit.agreesWithDsc_of_recursions` with the path unpacked. -/
theorem eq_dsc_of_recursions (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {R : ℚ → Finset (ℕ × ℕ) → Total L} (hACD : SweepRecursionACD q u a b N R)
    (hBE : SweepRecursionBE q u a b N R) (hB0 : SweepRecursionBOrigin q a b N R)
    (hUn : SweepRecursionUnswept a b N R) (hinit : SweepInitialCondition a b N R)
    {η : ℚ} (hη : IsAdmissibleLevel η) {c : Finset (ℕ × ℕ)}
    (hc : IsAdmissibleColouring a b N η c) : R η c = dsc q u a b N η c := by
  obtain ⟨y, hy, rfl⟩ := hc
  exact agreesWithDsc_of_recursions q u ha hb hN hACD hBE hB0 hUn hinit hη y hy

/-- **The iteration reaches the separating levels.** `HJO.Mellit.sepLevel a N` is admissible
(`HJO.Mellit.isAdmissibleLevel_sepLevel`), so it is one of the levels
`HJO.Mellit.eq_dsc_of_recursions` covers.

This is recorded because it is the level at which
`HJO.Mellit.braidValueColouring_eq_dsc_floor` is used —
`HJO.Mellit.invFin_eq_invIni_of_separatesDiagonal` makes the inversion prefactor vanish exactly
there, and `HJO.Mellit.dsc_compColouring_congr_level` moves the invariant between separating levels.
Nothing extra is needed to get there: the induction passes through every admissible level, so a
separating one is not a further obligation. -/
theorem eq_dsc_sepLevel (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {R : ℚ → Finset (ℕ × ℕ) → Total L} (hACD : SweepRecursionACD q u a b N R)
    (hBE : SweepRecursionBE q u a b N R) (hB0 : SweepRecursionBOrigin q a b N R)
    (hUn : SweepRecursionUnswept a b N R) (hinit : SweepInitialCondition a b N R)
    {c : Finset (ℕ × ℕ)} (hc : IsAdmissibleColouring a b N (sepLevel a N) c) :
    R (sepLevel a N) c = dsc q u a b N (sepLevel a N) c :=
  eq_dsc_of_recursions q u ha hb hN hACD hBE hB0 hUn hinit (isAdmissibleLevel_sepLevel a N) hc

/-- **The conclusion is about a configuration that occurs, at a nonempty colouring and in range.**
On the `2 × 3` rectangle — coprime, with `1 < a < b` — the level `7/2` is admissible and
`{(0,0), (1,3)}` is the colouring there of the above-diagonal path `(0,2,3)`
(`HJO.Mellit.colouring_thm42_be_witness`), so `HJO.Mellit.eq_dsc_of_recursions` pins the candidate
down at a colouring with two elements.

This is the check that the principle is not a statement about the empty colouring alone. Its force
is in the pairing with `HJO.Mellit.dsc_recursions`: the five hypotheses are simultaneously
satisfiable, here at `a = 2`, `b = 3`, `N = 1`, and the conclusion at that instance is not
vacuous. -/
theorem eq_dsc_of_recursions_example (q u : L) {R : ℚ → Finset (ℕ × ℕ) → Total L}
    (hACD : SweepRecursionACD q u 2 3 1 R) (hBE : SweepRecursionBE q u 2 3 1 R)
    (hB0 : SweepRecursionBOrigin q 2 3 1 R) (hUn : SweepRecursionUnswept 2 3 1 R)
    (hinit : SweepInitialCondition 2 3 1 R) :
    R (7 / 2) {(0, 0), (1, 3)} = dsc q u 2 3 1 (7 / 2) {(0, 0), (1, 3)} :=
  eq_dsc_of_recursions q u (by norm_num) (by norm_num) (by norm_num) hACD hBE hB0 hUn hinit
    ⟨3, by norm_num⟩ ⟨(![0, 2, 3] : Heights 2 3 1), by decide, colouring_thm42_be_witness.1⟩

/-- **The four clauses and the initial condition are consistent**, `HJO.Mellit.dsc` satisfying all
five. Read with `HJO.Mellit.agreesWithDsc_of_recursions` this says the principle is not a statement
about an empty class of candidates; read on its own it is the left-hand side of Mellit's Theorem 5.8
discharging its own half of the closing sentence. -/
theorem dsc_recursions (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    SweepRecursionACD q u a b N (dsc q u a b N) ∧ SweepRecursionBE q u a b N (dsc q u a b N) ∧
      SweepRecursionBOrigin q a b N (dsc q u a b N) ∧
      SweepRecursionUnswept a b N (dsc q u a b N) ∧
      SweepInitialCondition a b N (dsc q u a b N) :=
  ⟨dsc_sweepRecursionACD q u ha hb hN, dsc_sweepRecursionBE q u ha hb hN,
    dsc_sweepRecursionBOrigin q u ha hb hN, dsc_sweepRecursionUnswept q u ha hb hN,
    dsc_sweepInitialCondition q u ha⟩

end HJO.Mellit

end
