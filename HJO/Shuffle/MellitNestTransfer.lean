/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitSlopeTwoRow
public import HJO.Shuffle.MellitCollinearSplit

/-! # Applying a slope operator to a non-vacuum vector is free: `C` intertwines

`HJO.Mellit.qop_double_apply_one_of_lhsWord` (`HJO/Shuffle/MellitLhsCompInduction.lean`) reads
the clause of `HJO.Mellit.lhsRewrite_sweepWitness` at the two-part composition `α = (1,1)` and finds
two things on the `Λ` side that the singleton clause does not have: the *iterated* application
`Q_{a,b}(Q_{a,b}1)`, and the operator `Q_{2a,2b}` at the doubled, hence non-coprime, slope. One
might expect the first of these to be an obstruction, on the ground that the single-slope clause
delivers only a *single* application to the *vacuum*.

That is not so, as this file shows.

## `LhsSlope` is already the intertwining statement

`HJO.Mellit.LhsSlope q u a b` quantifies over every `f ∈ Λ`, and its right-hand side depends on `f`
only through `MvPolynomial.C f`, because `HJO.Mellit.slopeArg q u f = y_1d^*_+{}^{(0)}(Cf)`. Naming
that dependence `HJO.Sweep.sweepStep q u a b` — an operator on the *sweep* space, not on `Λ` — the
clause says exactly

`C(Q_{a,b}f) = sweepStep_{a,b}(Cf)`,

i.e. that `C` intertwines `Q_{a,b}` with `sweepStep_{a,b}`
(`HJO.Sweep.lhsSlope_iff_forall_sweepStep`, which is `Iff.rfl`). Intertwiners compose, so nesting is
free: `HJO.Sweep.c_qopWord_eq_sweepNest` computes `C` of an *arbitrary word* of slope operators as
the matching nest of `sweepStep`s, at any depth and at a general input, from nothing but `LhsSlope`
at each letter. There is no vacuum-only restriction anywhere, and in particular no obstruction of
the form "the single-slope clauses only evaluate `Q(1)`".

## The whole `(2,b)` row: the doubled slope collapses into proved slopes

The doubled slope is likewise not an extra unknown on the row `HJO.Sweep.lhsSlope_two_odd` closes.
At `(a,b) = (2,2k+1)` the doubled slope is `(4, 4k+2)`, whose primitive pair is `(2,2k+1)` and whose
split is therefore `(1,k)` (`HJO.Sweep.slopeSplit_four_row`), so `HJO.Sym.Qop`'s own non-coprime
branch gives `Q_{4,4k+2} = M^{-1}[Q_{3,3k+2}, D_k]`; and `HJO.Sweep.qop_three_of_mod_two` —
hypothesis-free — gives `Q_{3,3k+2} = M^{-1}[D_{k+1}, Q_{2,2k+1}]`. Composing,

`Q_{4,4k+2} = M^{-2}(D_{k+1}Q_{2,2k+1}D_k - Q_{2,2k+1}D_{k+1}D_k - D_kD_{k+1}Q_{2,2k+1}`
`  + D_kQ_{2,2k+1}D_{k+1})`

(`HJO.Sweep.qop_four_row_eq_words`), a sum of four words of length three in the three slopes
`(1,k)`, `(1,k+1)` and `(2,2k+1)` — and `LhsSlope` is proved at all three, the first two by the
hypothesis-free `HJO.Mellit.lhsSlope_one_left` and the third by the `(2,b)` row. So on the whole
`(2,b)` row *both* `Λ`-side terms of the two-part clause are sweep values
(`HJO.Sweep.c_clause_lhs_row_eq_sweepNest`), the iterated one included.

## What is actually left

`HJO.Sweep.sweepNest_residual_of_lhsWord_row` is the consequence: on the whole `(2,b)` row the
clause at `α = (1,1)` is, with the `Λ` side entirely eliminated, a statement *purely about the sweep
side* —

`(u+1)·(nest at (2,2k+1) twice) + u(q-1)M^{-2}·(four nests of length three)`
`  = (qu+1)·C(ct(d_-^2G_{2,1}G_{1,1}1))`.

Everything on the left is `HJO.Sweep.sweepStep` iterated: each application collapses to `Λ` and
re-enters the sweep space through `C`, so every nest lives at **level one**. The right-hand side is
the level-two composition word.

`HJO.Sweep.sweepNest_residual_peeled_of_lhsWord_row` names the difference exactly. Peeling the
level-two word with `HJO.Mellit.constantCoeff_lowerRun_stageWordTotal_append` at `β = (1)` and
`A = 1` turns the right-hand side into `ct(d_-^{(1)}(d_-^{(2)}G_{2,1}(G_{1,1}1)))`, so the one thing
standing between the level-one nests and the clause is an evaluation of the level-raising
operator `d_-^{(2)}G_{2,1}` on the image of `G_{1,1}` — at `A = 1` the stage with no `Z` factor,
`d_-^{(2)}T_{2↘1}Ω(1;a,b)`. That, and not the iterated application and not the non-coprime slope,
is the input `HJO.Mellit.LhsComputes` is missing; it is the question
`HJO.Mellit.constantCoeff_lowerRun_stageWordTotal_append`'s own docstring poses, and the same
phenomenon as `HJO.Mellit.NTermGlue`, whose reduction `HJO.Mellit.nTermGlue_iff_lhsSlope` is
circular.

## The collapse of the doubled slope is special to `a = 2`

At a general coprime `(a,b)` the doubled slope splits as
`Q_{2a,2b} = M^{-1}[Q_{2a-r,2b-s}, Q_{r,s}]` with `(r,s)` the primitive split and `r < a`
(`HJO.Sym.primitiveSplit_fst_lt`), so the complement has first coordinate `2a - r > a`: strictly
past the row it came from. At `a = 2` that is `4 - 1 = 3`, and
`HJO.Sweep.qop_three_of_mod_two` carries `a = 3` back into the `(2,b)` row — which is why the
collapse closes here. At `a = 3` it is `6 - r ∈ {4,5}`, and no `a = 4` or `a = 5` reduction is
proved; at `(3,4)`, whose primitive split is `(1,1)` (`HJO.Sweep.split_three_low`), the doubled
slope is `M^{-1}[Q_{5,7}, D_1]` and `Q_{5,7}` is outside everything. So this file closes the `Λ`
side of the two-part clause on the `(2,b)` row and nowhere else.

## The status of what is proved here

`HJO.Sweep.c_qopWord_eq_sweepNest` and `HJO.Sweep.c_clause_lhs_row_eq_sweepNest` are unconditional
at the slopes in question: their hypotheses are the sweep side's own genericity, already discharged
by `HJO.Sweep.lhsSlope_two_odd` and `HJO.Mellit.lhsSlope_one_left`.
`HJO.Sweep.qop_four_row_eq_words` carries no hypothesis at all. The two residual theorems are
different in kind: they assume `HJO.Mellit.LhsWord`, which is what is wanted, so they prove nothing
about it — they say what the clause asserts once its `Λ` side is eliminated, and so name the one
operator a proof along these lines would still have to evaluate.

## Genericity

`HJO.Sweep.sweepStep`, `lhsSlope_iff_forall_sweepStep`, `qopWord`, `sweepNest`,
`c_qopWord_eq_sweepNest`, `slopeSplit_four_row`, `qop_three_row`, `qop_four_row` and
`qop_four_row_eq_words`: **none**, not even `q ≠ 0` — `M^{-1}` is carried symbolically throughout.
`lhsSlope_two_row` and everything downstream of it inherit `HJO.Sweep.lhsSlope_two_odd`'s
`M ≠ 0`, `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, and the residual additionally
`HJO.Mellit.theta_copComp_one_one`'s `qu ≠ 0` and `qu ≠ 1`. None of these is removable: `q ≠ 0`,
`u ≠ 0` and `q ≠ 1` are the sweep side's own, the letter `Z = (qu)^{-1}z_1` being the zero map at
each.

## Implementation notes

Of the three inputs the two-part case of `HJO.Mellit.lhsRewrite_sweepWitness` appears to need, this
file supplies two and isolates the third; `HJO.Mellit.lhsRewrite_sweepWitness` itself is proved by
a different route (`HJO/Shuffle/ShuffleClosed.lean`).
-/

@[expose] public section

namespace HJO.Sweep

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {a b k : ℕ}

/-! ### `LhsSlope` is an intertwining relation, so nesting is free -/

/-- **The sweep side of one slope, as an operator on the sweep space.** `HJO.Mellit.LhsSlope`'s
right-hand side depends on `f` only through `Cf`, so it factors through this. -/
noncomputable def sweepStep (q u : L) (a b : ℕ) (w : Total L) : Total L :=
  (-1 : L) ^ (b + 1) • dminus q 1 (slopeOperator q u 1 a b
    ((auxVar 1 : Total L) * dplusStar q u 0 w))

/-- **`HJO.Mellit.LhsSlope` says exactly that `C` intertwines `Q_{a,b}` with `sweepStep_{a,b}`.**
Definitionally — the proof is `Iff.rfl`. This is the whole reason the iterated application costs
nothing. -/
@[hjo "lem_lhs_slope_intertwines"]
theorem lhsSlope_iff_forall_sweepStep :
    Mellit.LhsSlope q u a b ↔
      ∀ f : Sym.Lambda L, (MvPolynomial.C (Sym.Qop q u a b f) : Total L)
        = sweepStep q u a b (MvPolynomial.C f) := Iff.rfl

/-- A word of slope operators, composed on `Λ`; the head of the list is applied last. -/
noncomputable def qopWord (q u : L) : List (ℕ × ℕ) → Module.End L (Sym.Lambda L)
  | [] => 1
  | p :: ps => Sym.Qop q u p.1 p.2 * qopWord q u ps

/-- The matching nest of sweep steps. -/
noncomputable def sweepNest (q u : L) : List (ℕ × ℕ) → Total L → Total L
  | [] => fun w => w
  | p :: ps => fun w => sweepStep q u p.1 p.2 (sweepNest q u ps w)

/-- **Nesting is free.** If `HJO.Mellit.LhsSlope` holds at every letter of a word of slopes then the
sweep side computes the whole composite, at arbitrary depth and at a general input `f`. Intertwiners
compose; there is nothing else in the proof.

So no result of this kind is restricted to a *single* application, nor to the vacuum: the
clause at a slope, stated at a general `f`, already delivers `Q(Q(\cdots Q f))`. -/
@[hjo "lem_lhs_slope_intertwines"]
theorem c_qopWord_eq_sweepNest {ws : List (ℕ × ℕ)}
    (h : ∀ p ∈ ws, Mellit.LhsSlope q u p.1 p.2) (f : Sym.Lambda L) :
    (MvPolynomial.C (qopWord q u ws f) : Total L) = sweepNest q u ws (MvPolynomial.C f) := by
  induction ws with
  | nil => simp only [qopWord, sweepNest, Module.End.one_apply]
  | cons p ps ih =>
    rw [qopWord, sweepNest, Module.End.mul_apply,
      lhsSlope_iff_forall_sweepStep.1 (h p List.mem_cons_self) (qopWord q u ps f),
      ih fun r hr => h r (List.mem_cons_of_mem _ hr)]

/-! ### The doubled slope of the `(2,b)` row is a word in proved slopes -/

/-- `Q_{3,3k+2} = M^{-1}[D_{k+1}, Q_{2,2k+1}]`, `HJO.Sweep.qop_three_of_mod_two` restated at the
index the row uses. No hypothesis on `q`, `u` or `M`. -/
theorem qop_three_row (q u : L) (k : ℕ) :
    Sym.Qop q u 3 (3 * k + 2) = ((1 - q) * (1 - u))⁻¹ •
      (Sym.Dop q u (k + 1) * Sym.Qop q u 2 (2 * k + 1)
        - Sym.Qop q u 2 (2 * k + 1) * Sym.Dop q u (k + 1)) :=
  qop_three_of_mod_two k

/-- **The split of the doubled slope of the `(2,b)` row is `(1,k)`.** `\gcd(4, 4k+2) = 2`, so the
primitive pair is `(2, 2k+1)` and `slopeSplit` is its primitive split, which is
`HJO.Sweep.split_two_odd`. -/
theorem slopeSplit_four_row (hk : 1 ≤ k) : Sym.slopeSplit 4 (4 * k + 2) = ((1 : ℕ), k) := by
  have hcp : Nat.Coprime 2 (2 * k + 1) := (Nat.prime_two.coprime_iff_not_dvd).2 (by omega)
  have hg : Nat.gcd 4 (4 * k + 2) = 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, show 2 * 2 * k + 2 = 2 * (2 * k + 1) from by ring,
      Nat.gcd_mul_left, hcp, Nat.mul_one]
  rw [Sym.slopeSplit, hg, show (4 : ℕ) / 2 = 2 from rfl,
    show (4 * k + 2) / 2 = 2 * k + 1 from by omega, Sym.primitiveSplit]
  split_ifs with h1 h2
  · omega
  · omega
  · exact split_two_odd hk

/-- **The doubled slope of the `(2,b)` row is a commutator of `Q_{3,3k+2}` with a basic operator.**
`HJO.Sym.Qop`'s own non-coprime branch, with the split identified by
`HJO.Sweep.slopeSplit_four_row`. No hypothesis on `q`, `u` or `M`. -/
theorem qop_four_row (q u : L) (hk : 1 ≤ k) :
    Sym.Qop q u 4 (4 * k + 2) = ((1 - q) * (1 - u))⁻¹ •
      (Sym.Qop q u 3 (3 * k + 2) * Sym.Dop q u k
        - Sym.Dop q u k * Sym.Qop q u 3 (3 * k + 2)) := by
  have h := Sym.qop_eq_bracket q u (m := 4) (n := 4 * k + 2) (by omega) (by omega)
    (by
      intro hco
      have h2 : (2 : ℕ) ∣ Nat.gcd 4 (4 * k + 2) :=
        Nat.dvd_gcd (by omega) ⟨2 * k + 1, by ring⟩
      rw [Nat.Coprime] at hco
      omega)
  rw [slopeSplit_four_row hk] at h
  dsimp only at h
  rw [show (4 : ℕ) - 1 = 3 from rfl, show 4 * k + 2 - k = 3 * k + 2 from by omega,
    Sym.qop_one] at h
  exact h

/-- **The doubled slope of the `(2,b)` row is a sum of four words of length three in the slopes
`(1,k)`, `(1,k+1)` and `(2,2k+1)`.** No hypothesis on `q`, `u` or `M`. -/
theorem qop_four_row_eq_words (q u : L) (hk : 1 ≤ k) :
    Sym.Qop q u 4 (4 * k + 2) = (((1 - q) * (1 - u))⁻¹ * ((1 - q) * (1 - u))⁻¹) •
      (qopWord q u [(1, k + 1), (2, 2 * k + 1), (1, k)]
        - qopWord q u [(2, 2 * k + 1), (1, k + 1), (1, k)]
        - qopWord q u [(1, k), (1, k + 1), (2, 2 * k + 1)]
        + qopWord q u [(1, k), (2, 2 * k + 1), (1, k + 1)]) := by
  rw [qop_four_row q u hk, qop_three_row q u k]
  simp only [qopWord, Sym.qop_one, mul_one]
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, smul_smul]
  congr 1
  noncomm_ring

/-! ### The three slopes are exactly the ones already proved at a general `f` -/

/-- `HJO.Mellit.LhsSlope q u 2 (2k+1)`, `HJO.Sweep.lhsSlope_two_odd` named for use below. -/
theorem lhsSlope_two_row (hM : (1 - q) * (1 - u) ≠ 0) (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) (hk : 1 ≤ k) : Mellit.LhsSlope q u 2 (2 * k + 1) :=
  lhsSlope_two_odd hM hq0 hu0 hq1 hk

/-- **Every slope occurring in `HJO.Sweep.qop_four_row_eq_words` has `LhsSlope` at a general `f`**:
`(1,k)` and `(1,k+1)` by the hypothesis-free `HJO.Mellit.lhsSlope_one_left`, and `(2,2k+1)` by the
`(2,b)` row. -/
theorem lhsSlope_of_mem_row (hM : (1 - q) * (1 - u) ≠ 0) (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) (hk : 1 ≤ k) {ws : List (ℕ × ℕ)}
    (hws : ∀ p ∈ ws, p = ((1 : ℕ), k) ∨ p = ((1 : ℕ), k + 1) ∨ p = ((2 : ℕ), 2 * k + 1)) :
    ∀ p ∈ ws, Mellit.LhsSlope q u p.1 p.2 := by
  intro p hp
  rcases hws p hp with h | h | h <;> subst h
  · exact Mellit.lhsSlope_one_left q u hk
  · exact Mellit.lhsSlope_one_left q u (by omega)
  · exact lhsSlope_two_row hM hq0 hu0 hq1 hk

/-! ### The `Λ` side of the two-part clause on the `(2,b)` row, computed by the sweep side -/

/-- **Both `Λ`-side terms of the clause at `α = (1,1)` are sweep values, on the whole `(2,b)`
row.**

The left member is the *iterated* application `Q_{2,2k+1}(Q_{2,2k+1}1)` and the right is the
doubled, non-coprime slope `Q_{4,4k+2}(1)`; between them they are the entire `Λ` side of
`HJO.Mellit.qop_double_apply_one_of_lhsWord` at `(a,b) = (2,2k+1)`. Every term on the right is a
nest of the sweep words `HJO.Mellit.LhsSlope` already supplies at a general `f`, at the three slopes
`(1,k)`, `(1,k+1)` and `(2,2k+1)`. No slope operator outside that list occurs, and no application
to the vacuum is assumed of any of them. -/
theorem c_clause_lhs_row_eq_sweepNest (hM : (1 - q) * (1 - u) ≠ 0) (hq0 : q ≠ 0)
    (hu0 : u ≠ 0) (hq1 : q ≠ 1) (hk : 1 ≤ k) :
    (u + 1) • (MvPolynomial.C (Sym.Qop q u 2 (2 * k + 1)
          (Sym.Qop q u 2 (2 * k + 1) (1 : Sym.Lambda L))) : Total L)
        + (u * (q - 1)) • (MvPolynomial.C (Sym.Qop q u 4 (4 * k + 2) (1 : Sym.Lambda L)) : Total L)
      = (u + 1) • sweepNest q u [(2, 2 * k + 1), (2, 2 * k + 1)] 1
        + (u * (q - 1) * (((1 - q) * (1 - u))⁻¹ * ((1 - q) * (1 - u))⁻¹)) •
            (sweepNest q u [(1, k + 1), (2, 2 * k + 1), (1, k)] 1
              - sweepNest q u [(2, 2 * k + 1), (1, k + 1), (1, k)] 1
              - sweepNest q u [(1, k), (1, k + 1), (2, 2 * k + 1)] 1
              + sweepNest q u [(1, k), (2, 2 * k + 1), (1, k + 1)] 1) := by
  have hone : (MvPolynomial.C (1 : Sym.Lambda L) : Total L) = 1 := map_one _
  have hw : ∀ ws : List (ℕ × ℕ),
      (∀ p ∈ ws, p = ((1 : ℕ), k) ∨ p = ((1 : ℕ), k + 1) ∨ p = ((2 : ℕ), 2 * k + 1)) →
      (MvPolynomial.C (qopWord q u ws (1 : Sym.Lambda L)) : Total L) = sweepNest q u ws 1 := by
    intro ws hws
    rw [c_qopWord_eq_sweepNest (lhsSlope_of_mem_row hM hq0 hu0 hq1 hk hws) (1 : Sym.Lambda L),
      hone]
  have hsq : (MvPolynomial.C (Sym.Qop q u 2 (2 * k + 1)
        (Sym.Qop q u 2 (2 * k + 1) (1 : Sym.Lambda L))) : Total L)
      = sweepNest q u [(2, 2 * k + 1), (2, 2 * k + 1)] 1 := by
    rw [← hw [(2, 2 * k + 1), (2, 2 * k + 1)] (by simp)]
    simp only [qopWord, Module.End.mul_apply, Module.End.one_apply]
  have h4 := congrArg (fun T : Module.End L (Sym.Lambda L) => T (1 : Sym.Lambda L))
    (qop_four_row_eq_words (L := L) q u hk)
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply] at h4
  rw [hsq, h4, C_smul, map_add, map_sub, map_sub,
    hw [(1, k + 1), (2, 2 * k + 1), (1, k)] (by simp),
    hw [(2, 2 * k + 1), (1, k + 1), (1, k)] (by simp),
    hw [(1, k), (1, k + 1), (2, 2 * k + 1)] (by simp),
    hw [(1, k), (2, 2 * k + 1), (1, k + 1)] (by simp), smul_smul]

/-! ### The residual, with the `Λ` side eliminated -/

/-- **The two-part clause on the whole `(2,b)` row, as a pure sweep identity.**

`HJO.Mellit.qop_double_apply_one_of_lhsWord` at `(a,b) = (2,2k+1)` reads the clause of
`HJO.Mellit.lhsRewrite_sweepWitness` at `α = (1,1)` as an identity in `Λ`;
`HJO.Sweep.c_clause_lhs_row_eq_sweepNest` replaces both of its `Λ`-side terms by nests of the sweep
words already proved at a general `f`. Nothing about the `Λ` side survives: what the clause asserts
at `α = (1,1)` is that a fixed combination of **level-one** sweep nests equals `(qu+1)` times the
**level-two** composition word `ct(d_-^2G_{2,1}G_{1,1}1)`.

This is the residual, and it is where the remaining difficulty sits — not in the iterated
application, which `HJO.Sweep.c_qopWord_eq_sweepNest` supplies for free, and not in the
non-coprime doubled slope, which `HJO.Sweep.qop_four_row_eq_words` writes out in proved slopes. Each
`HJO.Sweep.sweepStep` collapses to `Λ` and re-enters the sweep space through `C`, so every nest on
the left lives at level one, while the right-hand side is a level-two quantity that is never taken
apart into level-one words here. -/
theorem sweepNest_residual_of_lhsWord_row (hM : (1 - q) * (1 - u) ≠ 0) (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1) (hk : 1 ≤ k)
    {Θ : Sym.Lambda L →ₐ[L] Module.End L (Sym.Lambda L)} (hΘ : IsSlopeHom 2 (2 * k + 1) q u Θ)
    (h : Mellit.LhsWord q u 2 (2 * k + 1)) :
    (u + 1) • sweepNest q u [(2, 2 * k + 1), (2, 2 * k + 1)] 1
        + (u * (q - 1) * (((1 - q) * (1 - u))⁻¹ * ((1 - q) * (1 - u))⁻¹)) •
            (sweepNest q u [(1, k + 1), (2, 2 * k + 1), (1, k)] 1
              - sweepNest q u [(2, 2 * k + 1), (1, k + 1), (1, k)] 1
              - sweepNest q u [(1, k), (1, k + 1), (2, 2 * k + 1)] 1
              + sweepNest q u [(1, k), (2, 2 * k + 1), (1, k + 1)] 1)
      = (q * u + 1) • (MvPolynomial.C (MvPolynomial.constantCoeff
          (Mellit.lowerRun q 2 (Mellit.stageWordTotal q u 2 (2 * k + 1) [1, 1]))) : Total L) := by
  have key := Mellit.qop_double_apply_one_of_lhsWord hv0 hv1 hΘ h
  rw [show 2 * 2 = 4 from rfl, show (2 * k + 1) * 2 = 4 * k + 2 from by ring] at key
  have hC := congrArg (fun g : Sym.Lambda L => (MvPolynomial.C g : Total L)) key
  simp only [map_add, C_smul] at hC
  rw [← c_clause_lhs_row_eq_sweepNest hM hq0 hu0 hq1 hk]
  exact hC

/-- **The residual, peeled onto the single operator that is missing.**

`HJO.Mellit.constantCoeff_lowerRun_stageWordTotal_append` at `β = (1)`, `A = 1` peels the level-two
word: `lowerRun`'s outermost `d_-` is the one immediately above the stage the append lemma peels. So
the right-hand side of `HJO.Sweep.sweepNest_residual_of_lhsWord_row` is

`ct(d_-^{(1)}(d_-^{(2)}G_{2,1}(G_{1,1}1)))`,

and the whole difference between it and the level-one nests on the left is the single operator
`d_-^{(2)}G_{2,1}` on `V_1` — which at `A = 1` is `d_-^{(2)}T_{2↘1}Ω(1;a,b)`, the stage with no
`Z` factor at all (`HJO.Mellit.stageTotal`).

**This is the precise input `HJO.Mellit.LhsComputes` lacks.** It is not the iterated application
(`HJO.Sweep.c_qopWord_eq_sweepNest`), and it is not the non-coprime doubled slope
(`HJO.Sweep.qop_four_row_eq_words`): it is an evaluation of one level-raising stage on the image of
another, and the general-`f` clauses cannot supply it because every `HJO.Sweep.sweepStep` returns to
level one through `C`. -/
theorem sweepNest_residual_peeled_of_lhsWord_row (hM : (1 - q) * (1 - u) ≠ 0) (hq0 : q ≠ 0)
    (hu0 : u ≠ 0) (hq1 : q ≠ 1) (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1) (hk : 1 ≤ k)
    {Θ : Sym.Lambda L →ₐ[L] Module.End L (Sym.Lambda L)} (hΘ : IsSlopeHom 2 (2 * k + 1) q u Θ)
    (h : Mellit.LhsWord q u 2 (2 * k + 1)) :
    (u + 1) • sweepNest q u [(2, 2 * k + 1), (2, 2 * k + 1)] 1
        + (u * (q - 1) * (((1 - q) * (1 - u))⁻¹ * ((1 - q) * (1 - u))⁻¹)) •
            (sweepNest q u [(1, k + 1), (2, 2 * k + 1), (1, k)] 1
              - sweepNest q u [(2, 2 * k + 1), (1, k + 1), (1, k)] 1
              - sweepNest q u [(1, k), (1, k + 1), (2, 2 * k + 1)] 1
              + sweepNest q u [(1, k), (2, 2 * k + 1), (1, k + 1)] 1)
      = (q * u + 1) • (MvPolynomial.C (MvPolynomial.constantCoeff
          (Mellit.lowerRun q 1 (dminus q 2 (Mellit.stageTotal q u 2 (2 * k + 1) 1 1
            (Mellit.stageWordTotal q u 2 (2 * k + 1) [1]))))) : Total L) := by
  have h2 := Mellit.constantCoeff_lowerRun_stageWordTotal_append q u 2 (2 * k + 1) [1] 1
  rw [show ([1] : List ℕ).length = 1 from rfl, show ([1] : List ℕ) ++ [1] = [1, 1] from rfl,
    show 1 + 1 = 2 from rfl] at h2
  rw [sweepNest_residual_of_lhsWord_row hM hq0 hu0 hq1 hv0 hv1 hk hΘ h, h2]

end HJO.Sweep

end
