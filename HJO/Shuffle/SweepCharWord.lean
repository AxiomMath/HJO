/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.Colouring
public import HJO.Shuffle.SweepQPower
public import HJO.Shuffle.SweepWordV0
public import HJO.SweepBlocks.PartnerCorner
public import HJO.CarlssonMellit.MarkedCharSeries
public import HJO.CarlssonMellit.MarkedWord
public import HJO.Classical.HomogeneousPreimage
public import HJO.Shuffle.MellitRem41
public meta import HJO.Attr

/-! # The scalar-free sweep word, and the summand the sweep computes

The sweep word `W(P̂)` of `HJO.Mellit.sweepWord` multiplies the five event operators `Φ_{P̂}(P)` of
`HJO.Mellit.sweepOperator` along the swept region in decreasing order of above-diagonal rank. Each
`Φ_{P̂}(P)` is a scalar in `𝕜` times a *scalar-free* operator: the `Ψ_{P̂}(P)`, which is
`d♭₊`, `d♭₋`, `Δ`, `id` according as the event type is `A`, `B`, `C`, `D`, `E`, the scalar
being `1`, `q^{-a_{P̂}(P)}`, `q^{a_{P̂}(P)}`, `u`. `Ψ` is not defined anywhere else, so it is
defined here, together with its composite along the same rank listing that `HJO.Mellit.sweepWord`
uses.

This file carries that factorisation, the first and the fifth paragraph of the proof of
`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar`, and the reduction of
`HJO.Mellit.sweepComputes` that the three of them give.

## Main definitions

* `HJO.Mellit.psiOperator`, `HJO.Mellit.psiWord`: the `Ψ_{P̂}(P)` and the composite
  `Ψ_{P̂}(P_M) ∘ ⋯ ∘ Ψ_{P̂}(P_1)` along the decreasing rank listing.
* `HJO.Mellit.sweepScalar`: the scalar by which `Φ_{P̂}(P)` exceeds `Ψ_{P̂}(P)`.
* `HJO.Mellit.markedPositions`, `HJO.Mellit.partnerPath`: `S(P̂)` in rank-order positions, and the
  square partner `P̂'` of `HJO.Dyck.attackPartner` as a coarea sequence on those positions.

## Main results

* `HJO.Mellit.sweepWord_eq_smul_psiWord`, and with the exponents evaluated
  `HJO.Mellit.sweepWord_eq_smul_psiWord_of_isAboveDiagonal`:
  `W(P̂) = u^{ârea(P̂)} q^{ĥ(P̂) - max t̂dinv(P̂)} · Ψ(P̂)`, the display in the middle of the
  proof of `HJO.Mellit.sweepComputes`.
* `HJO.Mellit.sweepChar_eq_pathMarkedCharSeries`: **the first paragraph of the proof of
  `HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar`**,
  `χ(P̂) = χ(P̂', S(P̂))`. No hypothesis beyond `HJO.Paths.IsAboveDiagonal`.
* `HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_of_map_eq_sweepChar`: **the fifth
  paragraph**, that the identity `ι(f) = χ(P̂)` forces `f` homogeneous of degree `bN`.
* `HJO.Mellit.constantCoeff_sweepWord_one_mem_lambdaComp_and_map_eq_smul_sweepChar_of_charWord`:
  `HJO.Mellit.sweepComputes` **modulo the conclusion of
  `HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar`**, carried as a
  hypothesis.
* `HJO.Mellit.map_constantCoeff_psiWord_eq_sweepChar_of_cor46`,
  `HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar_of_cor46`:
  `HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar` **modulo
  `HJO.Mellit.map_constantCoeff_markedWordOp'` and the identification of the two words** — the
  second, third and fourth paragraphs of its proof, carried as the single hypothesis
  `Ψ(P̂)(1) = Ξ_{P̂', S(P̂)}(1)`.
* `HJO.Mellit.sweepComputes_of_charWord`, `HJO.Mellit.sweepComputes_of_cor46`:
  `HJO.Mellit.SweepComputes` — one of the three hypotheses of `HJO.Mellit.shuffle_of_three` — from
  the same two open inputs and nothing else.

**Neither lemma is proved unconditionally in this file.**
`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar` and
`HJO.Mellit.sweepComputes` both still rest on `HJO.Mellit.map_constantCoeff_markedWordOp'` and on
the identification of the two words; see
`HJO.Mellit.map_constantCoeff_psiWord_eq_sweepChar_of_cor46` for the exact two hypotheses.

## Orientation

`HJO.Mellit.psiWord` is, like `HJO.Mellit.sweepWord`, the `List.prod` along
`HJO.Mellit.sortByRank a b N (HJO.Paths.sweptRegion y)`, the *increasing* rank listing. In
`Module.End` the rightmost factor of a product acts first, so that product is the composite
`Ψ_{P̂}(P_M) ∘ ⋯ ∘ Ψ_{P̂}(P_1)` against the *decreasing* listing `P_1, …, P_M`.
`HJO.Mellit.psiWord_eq_mul_of_reverse_eq_cons` states this exactly as
`HJO.Mellit.sweepWord_eq_mul_of_reverse_eq_cons` does for `W(P̂)`.

## Implementation notes

*`q ≠ 0` is needed and is not decoration.* Collecting the scalars in front of the composite
multiplies `q^{-a_{P̂}(P)}` over the type-`C` points against `q^{a_{P̂}(P)}` over the type-`D`
points, and reads the result as the single power `q^{Σ_D - Σ_C}`. That step is `zpow_add₀`, which
needs `q ≠ 0`: at `q = 0`, one type-`C` point with `a_{P̂} = 1` and one type-`D` point with
`a_{P̂} = 1` give `0^{-1} · 0^1 = 0` on the left and `0^0 = 1` on the right. The argument is
made over the coefficient field `𝕜 = ℚ(q, u)` (`q` and `u` are indeterminates), where `q` is
invertible, so this is that standing hypothesis made explicit and not a departure. Every consumer
has it: `HJO.Mellit.shuffle_of_three` asks for `SweepComputes` only under
`AlgebraicIndependent ℤ ![q, u]`, whence `q ≠ 0` by
`HJO.Mellit.ne_zero_of_algebraicIndependent_fst`.

*`V_0 = Λ` is read by `MvPolynomial.constantCoeff`.* The total space is
`MvPolynomial ℕ (HJO.Sym.Lambda L)`, in which `MvPolynomial.C` is the inclusion of `V_0` and
`MvPolynomial.constantCoeff` its retraction; `HJO.Mellit.sweepWord_mem_piece_zero` is what makes
that retraction lossless on `W(P̂)(1)`. The factorisation below needs no such membership:
`constantCoeff` is `L`-linear, so the scalar passes through it whatever graded piece the value lies
in.

*The hypothesis carried is the whole of
`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar`'s conclusion*, in the
encoding `HJO.Mellit.sweepComputes` needs it in: `constantCoeff (Ψ(P̂)(1))` is homogeneous of degree
`bN` and every realisation carries it to `χ(P̂)`. The `f = (Ψ_{P̂}(P_M) ∘ ⋯ ∘ Ψ_{P̂}(P_1))(1)` is
that constant coefficient.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, section "The sweep process". -/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {a b N : ℕ}

/-! ### The scalar-free event operator -/

/-- **The scalar-free event operator `Ψ_{P̂}(P)`.** The operator that
`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar` reads off an event:
`d♭₊`, `d♭₋`, `Δ`, `id` according as `ev_{P̂}(P)` is `A`, `B`, `C`, `D`, `E`, at the graded index
`k_{P̂}(P)` of `HJO.Paths.sweepWidth`.

This is `HJO.Mellit.sweepOperator` with the scalars of rules `C`, `D` and `E` removed, and
`HJO.Mellit.sweepOperator_eq_smul_psiOperator` is that statement. As there, the domain and codomain
are not types: the value is an endomorphism of the single space `HJO.Sweep.Total L`, and the
map `V_k → V_{k'}` is a pair of membership statements about `HJO.Sweep.piece`. Total in `P`
and in `y`, again as there. -/
noncomputable def psiOperator (q : L) (y : Heights a b N) (P : ℕ × ℕ) :
    Module.End L (Total L) :=
  match eventType y P with
  | EventType.A => dplus q (sweepWidth y P)
  | EventType.B => dminus q (sweepWidth y P)
  | EventType.C => corner q (sweepWidth y P)
  | EventType.D => 1
  | EventType.E => 1

/-- **The scalar of an event.** The factor by which `HJO.Mellit.sweepOperator` exceeds
`HJO.Mellit.psiOperator`: `1` at event types `A` and `B`, `q^{-a_{P̂}(P)}` at `C`,
`q^{a_{P̂}(P)}` at `D` and `u` at `E`, with `a_{P̂}(P)` the count `HJO.Paths.sweepRight`. The
exponent is an `ℤ` on both sides so that the two powers of `q` can be collected into one; at type
`D` that is the same scalar as the `ℕ` power `HJO.Mellit.sweepOperator` writes, by
`zpow_natCast`. -/
noncomputable def sweepScalar (q u : L) (y : Heights a b N) (P : ℕ × ℕ) : L :=
  match eventType y P with
  | EventType.A => 1
  | EventType.B => 1
  | EventType.C => q ^ (-(sweepRight y P : ℤ))
  | EventType.D => q ^ (sweepRight y P : ℤ)
  | EventType.E => u

/-- **Each event operator is a scalar times the scalar-free one.** The first sentence of the
proof of `HJO.Mellit.sweepComputes`. -/
theorem sweepOperator_eq_smul_psiOperator (q u : L) (y : Heights a b N) (P : ℕ × ℕ) :
    sweepOperator q u y P = sweepScalar q u y P • psiOperator q y P := by
  rcases h : eventType y P with _ | _ | _ | _ | _ <;>
    simp only [sweepOperator, psiOperator, sweepScalar, h, one_smul, zpow_natCast]

/-! ### The scalar-free sweep word -/

/-- **The scalar-free sweep word.** The composite
`Ψ_{P̂}(P_M) ∘ ⋯ ∘ Ψ_{P̂}(P_1)` of
`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar`, where `P_1, …, P_M`
lists `Sw(P̂)` in strictly decreasing order of above-diagonal rank.

Written, exactly as `HJO.Mellit.sweepWord` is, as the `List.prod` of the operators along the
*increasing* rank listing `HJO.Mellit.sortByRank a b N (HJO.Paths.sweptRegion y)`. **That is the
intended composite and not its opposite**: in `Module.End L (HJO.Sweep.Total L)` the product
`f * g` applies `g` first, so the rightmost factor — the operator of the highest-ranked point `P_1`
— acts first. `HJO.Mellit.psiWord_eq_mul_of_reverse_eq_cons` states this against the
decreasing listing. -/
noncomputable def psiWord (q : L) (y : Heights a b N) : Module.End L (Total L) :=
  ((sortByRank a b N (sweptRegion y)).map (psiOperator q y)).prod

/-- **The composition order of the scalar-free sweep word.** Let `P :: Ps` be the
listing of `Sw(P̂)` in decreasing rank, so that `P = P_1` is the highest-ranked swept point. Then
`Ψ(P̂) = (Ψ_{P̂}(P_r) ⋯ Ψ_{P̂}(P_2)) · Ψ_{P̂}(P)`: the factor of `P_1` stands rightmost, hence acts
first, which is the reading of `Ψ_{P̂}(P_M) ∘ ⋯ ∘ Ψ_{P̂}(P_1)`. The companion of
`HJO.Mellit.sweepWord_eq_mul_of_reverse_eq_cons`. -/
theorem psiWord_eq_mul_of_reverse_eq_cons (q : L) (y : Heights a b N) {P : ℕ × ℕ}
    {Ps : List (ℕ × ℕ)} (h : (sortByRank a b N (sweptRegion y)).reverse = P :: Ps) :
    psiWord q y = (Ps.reverse.map (psiOperator q y)).prod * psiOperator q y P := by
  have hasc : sortByRank a b N (sweptRegion y) = Ps.reverse ++ [P] := by
    rw [← List.reverse_reverse (sortByRank a b N (sweptRegion y)), h]
    simp
  rw [psiWord, hasc, List.map_append, List.prod_append]
  simp

/-! ### Collecting the scalars -/

omit [Algebra ℚ L] in
/-- The scalars of a list of scalar multiples collect in front of the product. -/
private theorem prod_map_smul {α : Type*} (c : α → L) (f : α → Module.End L (Total L)) :
    ∀ l : List α, (l.map fun x => c x • f x).prod = (l.map c).prod • (l.map f).prod := by
  intro l
  induction l with
  | nil => simp
  | cons x t ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, List.map_cons,
      List.prod_cons, Algebra.smul_mul_assoc, mul_smul_comm, smul_smul]

omit [Algebra ℚ L] in
/-- A product of `zpow`s of a nonzero base is the `zpow` of the sum. -/
private theorem prod_zpow_eq_zpow_sum {α : Type*} {q : L} (hq : q ≠ 0) (e : α → ℤ) :
    ∀ s : Finset α, ∏ x ∈ s, q ^ e x = q ^ ∑ x ∈ s, e x := by
  intro s
  induction s using Finset.cons_induction with
  | empty => simp
  | cons x s hx ih => rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ hq]

omit [Algebra ℚ L] in
/-- A product of powers of a fixed base is the power of the sum. -/
private theorem prod_pow_eq_pow_sum {α : Type*} (u : L) (e : α → ℕ) :
    ∀ s : Finset α, ∏ x ∈ s, u ^ e x = u ^ ∑ x ∈ s, e x := by
  intro s
  induction s using Finset.cons_induction with
  | empty => simp
  | cons x s hx ih => rw [Finset.prod_cons, Finset.sum_cons, ih, pow_add]

omit [Algebra ℚ L] in
/-- The product of a function over the rank listing of a finite set is its product over the set:
the listing is a permutation of `Finset.toList`. -/
private theorem prod_map_sortByRank (a b N : ℕ) (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → L) :
    ((sortByRank a b N s).map c).prod = ∏ P ∈ s, c P := by
  rw [((sortByRank_perm a b N s).map c).prod_eq, Finset.prod_map_toList]

omit [Algebra ℚ L] in
/-- **The scalars the sweep collects.** Their product over the swept region is
`u^{#E} q^{Σ_D - Σ_C}`, with `Σ_C` and `Σ_D` the sums of `a_{P̂}(P)` over the type-`C` and the
type-`D` points — the two quantities
`HJO.Paths.sum_sweepRight_D_sub_sum_sweepRight_C_eq_aboveHookCount_sub_aboveMaxTdinv` evaluates. -/
theorem prod_sweepScalar (q u : L) (hq : q ≠ 0) (y : Heights a b N) :
    ∏ P ∈ sweptRegion y, sweepScalar q u y P =
      u ^ #{P ∈ sweptRegion y | eventType y P = EventType.E} *
        q ^ (((∑ P ∈ {P ∈ sweptRegion y | eventType y P = EventType.D},
            sweepRight y P : ℕ) : ℤ) -
          ((∑ P ∈ {P ∈ sweptRegion y | eventType y P = EventType.C},
            sweepRight y P : ℕ) : ℤ)) := by
  classical
  set eE : ℕ × ℕ → ℕ := fun P => if eventType y P = EventType.E then 1 else 0 with heE
  set ex : ℕ × ℕ → ℤ := fun P => (if eventType y P = EventType.D then (sweepRight y P : ℤ) else 0) -
    (if eventType y P = EventType.C then (sweepRight y P : ℤ) else 0) with hex
  have hfac : ∀ P, sweepScalar q u y P = u ^ eE P * q ^ ex P := by
    intro P
    rcases h : eventType y P with _ | _ | _ | _ | _ <;>
      simp only [sweepScalar, heE, hex, h, reduceCtorEq, reduceIte, pow_zero, pow_one,
        zpow_zero, one_mul, mul_one, sub_zero, zero_sub]
  rw [Finset.prod_congr rfl fun P _ => hfac P, Finset.prod_mul_distrib,
    prod_pow_eq_pow_sum, prod_zpow_eq_zpow_sum hq]
  congr 1
  · rw [Finset.card_filter]
  · rw [Finset.sum_sub_distrib, ← Finset.sum_filter, ← Finset.sum_filter, Nat.cast_sum,
      Nat.cast_sum]

/-- **The sweep word is a scalar times the scalar-free sweep word.** The display in the middle of
the proof of `HJO.Mellit.sweepComputes`:
`W(P̂) = u^{#E} q^{Σ_D - Σ_C} (Ψ_{P̂}(P_M) ∘ ⋯ ∘ Ψ_{P̂}(P_1))`. -/
theorem sweepWord_eq_smul_psiWord (q u : L) (hq : q ≠ 0) (y : Heights a b N) :
    sweepWord q u y =
      (u ^ #{P ∈ sweptRegion y | eventType y P = EventType.E} *
        q ^ (((∑ P ∈ {P ∈ sweptRegion y | eventType y P = EventType.D}, sweepRight y P : ℕ) : ℤ) -
          ((∑ P ∈ {P ∈ sweptRegion y | eventType y P = EventType.C},
            sweepRight y P : ℕ) : ℤ))) • psiWord q y := by
  rw [sweepWord, psiWord,
    List.map_congr_left (fun P _ => sweepOperator_eq_smul_psiOperator q u y P),
    prod_map_smul, prod_map_sortByRank, prod_sweepScalar q u hq y]

/-- **The sweep word is a scalar times the scalar-free sweep word**, with the scalar evaluated by
`HJO.Paths.card_filter_eventType_E` and
`HJO.Paths.sum_sweepRight_D_sub_sum_sweepRight_C_eq_aboveHookCount_sub_aboveMaxTdinv`:
`W(P̂) = u^{ârea(P̂)} q^{ĥ(P̂) - max t̂dinv(P̂)} Ψ(P̂)` on an above-diagonal path. -/
theorem sweepWord_eq_smul_psiWord_of_isAboveDiagonal (q u : L) (hq : q ≠ 0)
    {y : Heights a b N} (hy : IsAboveDiagonal y) :
    sweepWord q u y =
      (u ^ aboveArea y * q ^ ((aboveHookCount y : ℤ) - (aboveMaxTdinv y : ℤ))) • psiWord q y := by
  rw [sweepWord_eq_smul_psiWord q u hq y, card_filter_eventType_E hy,
    sum_sweepRight_D_sub_sum_sweepRight_C_eq_aboveHookCount_sub_aboveMaxTdinv hy]

/-! ### The sweep process computes the summand -/

/-- **`HJO.Mellit.sweepComputes`, modulo the conclusion of
`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar`.** For an above-diagonal
`(aN, bN)`-path `y` and a realisation `ι`, the element `f = W(P̂)(1)` of `Λ` — read through
`MvPolynomial.constantCoeff`, as `HJO.Mellit.sweepWord_mem_piece_zero` licenses — is homogeneous of
degree `bN` and satisfies `ι(f) = u^{ârea(P̂)} q^{ĥ(P̂) - max t̂dinv(P̂)} χ(P̂)`.

The hypothesis `hcw` is the conclusion of
`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar` in the same encoding: the
element `(Ψ_{P̂}(P_M) ∘ ⋯ ∘ Ψ_{P̂}(P_1))(1)` of `Λ` is homogeneous of degree `bN` and every
realisation carries it to `χ(P̂)`. Given it, the whole of this lemma is the collection of the
scalars (`HJO.Mellit.sweepWord_eq_smul_psiWord`) together with the two evaluations of the collected
exponents, `HJO.Paths.card_filter_eventType_E` for `u` and
`HJO.Paths.sum_sweepRight_D_sub_sum_sweepRight_C_eq_aboveHookCount_sub_aboveMaxTdinv` for `q`.

`q ≠ 0` is the standing hypothesis on `𝕜 = ℚ(q, u)`, and it is needed: see the module
docstring for the two-point counterexample at `q = 0`. -/
theorem constantCoeff_sweepWord_one_mem_lambdaComp_and_map_eq_smul_sweepChar_of_charWord
    (q u : L) (hq : q ≠ 0) {y : Heights a b N} (hy : IsAboveDiagonal y)
    {ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L}
    (hcw : MvPolynomial.constantCoeff (psiWord q y (1 : Total L)) ∈ Sym.LambdaComp L (b * N) ∧
      ι (MvPolynomial.constantCoeff (psiWord q y (1 : Total L))) = sweepChar q y) :
    MvPolynomial.constantCoeff (sweepWord q u y (1 : Total L)) ∈ Sym.LambdaComp L (b * N) ∧
      ι (MvPolynomial.constantCoeff (sweepWord q u y (1 : Total L))) =
        (u ^ aboveArea y * q ^ ((aboveHookCount y : ℤ) - (aboveMaxTdinv y : ℤ))) •
          sweepChar q y := by
  have hval : MvPolynomial.constantCoeff (sweepWord q u y (1 : Total L)) =
      (u ^ aboveArea y * q ^ ((aboveHookCount y : ℤ) - (aboveMaxTdinv y : ℤ))) •
        MvPolynomial.constantCoeff (psiWord q y (1 : Total L)) := by
    rw [sweepWord_eq_smul_psiWord_of_isAboveDiagonal q u hq hy, LinearMap.smul_apply,
      MvPolynomial.constantCoeff_smul]
  refine ⟨hval ▸ Submodule.smul_mem _ _ hcw.1, ?_⟩
  rw [hval, map_smul, hcw.2]

/-! ### The two characteristic functions agree -/

/-- **The marked constraint set `S(P̂)` read in `0`-based rank-order positions.** The companion of
`HJO.Mellit.attackPositions`: `HJO.Paths.sweepMarked` indexes the pairs by foot heights, while the
Carlsson–Mellit side of `HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar`
indexes them by position in the increasing-rank listing, as `HJO.Dyck.corner` does. This is the
image of the first under the relabelling, so it is the same `S(P̂)` and not a second definition of
it. -/
def markedPositions (y : Heights a b N) : Finset (ℕ × ℕ) :=
  (sweepMarked y).image fun p => ((stepIndex y p.1 : ℕ), (stepIndex y p.2 : ℕ))

/-- **Membership in the relabelled constraint set, at a pair of north steps.** The relabelling is
faithful, neither losing nor inventing a pair; injectivity of `HJO.Paths.stepIndex` is what rules
out inventing one. -/
theorem mem_markedPositions {y : Heights a b N} (hy : IsAboveDiagonal y) (s t : Fin (b * N)) :
    (((stepIndex y s : ℕ), (stepIndex y t : ℕ)) ∈ markedPositions y) ↔ (s, t) ∈ sweepMarked y := by
  simp only [markedPositions, mem_image, Prod.ext_iff]
  constructor
  · rintro ⟨p, hp, h1, h2⟩
    have e1 : p.1 = s := stepIndex_injective hy (Fin.val_injective h1)
    have e2 : p.2 = t := stepIndex_injective hy (Fin.val_injective h2)
    rw [← e1, ← e2]
    exact hp
  · exact fun h => ⟨(s, t), h, rfl, rfl⟩

/-- Membership in the relabelled constraint set, at a pair of positions. -/
theorem mem_markedPositions_stepAt {y : Heights a b N} (hy : IsAboveDiagonal y)
    (p r : Fin (b * N)) :
    (((p : ℕ), (r : ℕ)) ∈ markedPositions y) ↔ (stepAt hy p, stepAt hy r) ∈ sweepMarked y := by
  have h := mem_markedPositions hy (stepAt hy p) (stepAt hy r)
  rwa [stepIndex_stepAt, stepIndex_stepAt] at h

/-- Membership in the relabelled attack set, at a pair of positions. -/
theorem mem_attackPositions_stepAt {y : Heights a b N} (hy : IsAboveDiagonal y)
    (p r : Fin (b * N)) :
    (((p : ℕ), (r : ℕ)) ∈ attackPositions y) ↔ (stepAt hy p, stepAt hy r) ∈ sweepAttack y := by
  have h := mem_attackPositions hy (stepAt hy p) (stepAt hy r)
  rwa [stepIndex_stepAt, stepIndex_stepAt] at h

/-- **The square partner `P̂'` of an above-diagonal path**, as a coarea sequence on the rank-order
positions: `HJO.Dyck.attackPartner` at the relabelled attack set. The `x'_j` for
`1 ≤ j ≤ bN` is the value at the position `j - 1`, positions being `0`-based. -/
noncomputable def partnerPath (y : Heights a b N) : Fin (b * N) → ℕ :=
  fun k => Dyck.attackPartner (attackPositions y) (k : ℕ)

/-- **`HJO.Dyck.isSquareDyck_and_attackSet_eq_of_isTransitiveAttackSet` at the square partner**:
`P̂'` is a square Dyck path of length `bN`. -/
theorem isSquareDyck_partnerPath {y : Heights a b N} (hy : IsAboveDiagonal y) :
    Dyck.IsSquareDyck (b * N) (partnerPath y) :=
  (Dyck.isSquareDyck_and_attackSet_eq_of_isTransitiveAttackSet
    (isTransitiveAttackSet_attackPositions hy) fun _ => rfl).1

/-- **`HJO.Dyck.isSquareDyck_and_attackSet_eq_of_isTransitiveAttackSet` at the square partner**:
`At(P̂') = 𝒜(P̂)`, the attack set of the partner is the attack set of the path, read in rank-order
positions. -/
theorem attackSet_partnerPath {y : Heights a b N} (hy : IsAboveDiagonal y) :
    Dyck.attackSet (partnerPath y) = attackPositions y :=
  (Dyck.isSquareDyck_and_attackSet_eq_of_isTransitiveAttackSet
    (isTransitiveAttackSet_attackPositions hy) fun _ => rfl).2

/-- **`S(P̂) ⊆ c(P̂')`: every marked pair is a corner of the square partner.** This is
`HJO.Paths.attackPartner_stepIndex_and_mem_corner_of_mem_sweepMarked`, as the containment the first
paragraph of the proof of `HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar`
uses. This is the containment that makes `HJO.Mellit.map_constantCoeff_markedWordOp'` applicable at
`π = P̂'` and `T = S(P̂)`. -/
theorem markedPositions_subset_corner {y : Heights a b N} (hy : IsAboveDiagonal y) :
    markedPositions y ⊆ Dyck.corner (partnerPath y) := by
  intro c hc
  simp only [markedPositions, mem_image] at hc
  obtain ⟨p, hp, rfl⟩ := hc
  exact (attackPartner_stepIndex_and_mem_corner_of_mem_sweepMarked hy hp).2

/-- **The two characteristic functions agree.** The first paragraph of the proof of
`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar`: `χ(P̂) = χ(P̂', S(P̂))`,
the characteristic function of the path of `HJO.Paths.sweepChar` and the marked characteristic
series of `HJO.Dyck.pathMarkedCharSeries` at the square partner and the relabelled constraint set.

Both sides sum over the words on the `bN` north steps subject to a strict descent along every pair
of the constraint set, weighted by `q` to the number of pairs of the attack set the word inverts.
The two constraint sets are the same set of pairs and the two attack sets are the same set of pairs,
`At(P̂') = 𝒜(P̂)` by `HJO.Dyck.isSquareDyck_and_attackSet_eq_of_isTransitiveAttackSet`; all that
separates the two displays is the relabelling `HJO.Paths.stepIndex` of the north steps by their
position in the increasing-rank listing, under which a sum over all words is a sum over all
words. -/
theorem sweepChar_eq_pathMarkedCharSeries {K : Type*} [CommRing K] (q : K)
    {y : Heights a b N} (hy : IsAboveDiagonal y) :
    sweepChar q y = Dyck.pathMarkedCharSeries q (partnerPath y) (markedPositions y) := by
  funext d
  rw [Dyck.pathMarkedCharSeries, attackSet_partnerPath hy]
  simp only [sweepChar, Dyck.markedCharSeries]
  refine Finset.sum_nbij' (i := fun w r => w (stepAt hy r)) (j := fun v i => v (stepIndex y i))
    ?_ ?_ ?_ ?_ ?_
  · -- the relabelled word is admissible
    intro w hw
    simp only [mem_filter, Fintype.mem_piFinset] at hw ⊢
    refine ⟨fun r => hw.1 _, ?_, fun p hp => ?_⟩
    · rw [Sym.wordExponent, ← hw.2.2]
      exact Fintype.sum_equiv (stepIndexEquiv hy).symm _ _ fun r => rfl
    · exact hw.2.1 _ ((mem_markedPositions_stepAt hy p.1 p.2).1 hp)
  · -- the inverse relabelling is admissible
    intro v hv
    simp only [mem_filter, Fintype.mem_piFinset] at hv ⊢
    refine ⟨fun i => hv.1 _, fun p hp => ?_, ?_⟩
    · refine hv.2.2 (stepIndex y p.1, stepIndex y p.2) ?_
      exact (mem_markedPositions hy p.1 p.2).2 hp
    · rw [← hv.2.1, Sym.wordExponent]
      exact Fintype.sum_equiv (stepIndexEquiv hy) _ _ fun i => rfl
  · exact fun w _ => funext fun i => by simp only [stepAt_stepIndex]
  · exact fun v _ => funext fun r => by simp only [stepIndex_stepAt]
  · -- the two exponents of `q` agree
    intro w _
    congr 1
    refine Finset.card_nbij' (i := fun p => (stepIndex y p.1, stepIndex y p.2))
      (j := fun p => (stepAt hy p.1, stepAt hy p.2)) ?_ ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_coe, mem_filter] at hp
      rw [Finset.mem_coe, Dyck.mem_invSet, mem_filter_univ]
      refine ⟨(mem_attackPositions hy p.1 p.2).2 hp.1, ?_⟩
      change w (stepAt hy (stepIndex y p.2)) < w (stepAt hy (stepIndex y p.1))
      rw [stepAt_stepIndex, stepAt_stepIndex]
      exact hp.2
    · intro p hp
      rw [Finset.mem_coe, Dyck.mem_invSet, mem_filter_univ] at hp
      rw [Finset.mem_coe, mem_filter]
      exact ⟨(mem_attackPositions_stepAt hy p.1 p.2).1 hp.1, hp.2⟩
    · exact fun p _ => Prod.ext (stepAt_stepIndex hy p.1) (stepAt_stepIndex hy p.2)
    · exact fun p _ => Prod.ext (stepIndex_stepAt hy p.1) (stepIndex_stepAt hy p.2)

/-! ### The degenerate rectangle -/

/-- **The marked characteristic series of the empty path is `1`.** At `n = 0` the only labelling is
the empty word: it inverts nothing and is marked by every `T`, so the series has coefficient `1` at
the empty monomial and `0` elsewhere. -/
theorem markedCharSeries_eq_one_of_eq_zero {K : Type*} [CommRing K] (q : K) {n : ℕ} (hn : n = 0)
    (R T : Finset (ℕ × ℕ)) : Dyck.markedCharSeries q n R T = (1 : Sym.AlphabetSeries K) := by
  subst hn
  refine MvPowerSeries.ext fun d => ?_
  rw [MvPowerSeries.coeff_one]
  rcases eq_or_ne d 0 with rfl | hd
  · have hmark : Dyck.IsMarkedLabelling T (fun _ : Fin 0 => 0) := fun p _ => p.1.elim0
    have h := Dyck.coeff_markedCharSeries_single q 0 R T 0
    simp only [Finsupp.single_zero, hmark, ite_true] at h
    simp [h]
  · have hne : (d.sum fun _ e => e) ≠ 0 := by
      intro hsum
      rw [Finsupp.sum] at hsum
      refine hd (Finsupp.ext fun i => ?_)
      by_cases hi : i ∈ d.support
      · exact absurd (Finset.sum_eq_zero_iff.1 hsum i hi) (Finsupp.mem_support_iff.1 hi)
      · simpa using Finsupp.notMem_support_iff.1 hi
    rw [Dyck.coeff_markedCharSeries_eq_zero_of_sum_ne hne]
    simp [hd]

/-- **The word of the empty path is the identity.** At `n = 0` the step word has no positions, so
`Ξ_{π,T}` is the empty product. -/
theorem markedWordOp_eq_one_of_eq_zero (q : L) {n : ℕ} (hn : n = 0) (x : Fin n → ℕ)
    (T : Finset (ℕ × ℕ)) : Sweep.markedWordOp q x T = 1 := by
  subst hn
  rw [Sweep.markedWordOp]
  simp

/-! ### `HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar` modulo
`HJO.Mellit.map_constantCoeff_markedWordOp'` -/

/-- **The second conjunct of
`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar`, modulo
`HJO.Mellit.map_constantCoeff_markedWordOp'` and the identification of the two words.**
`ι((Ψ_{P̂}(P_M) ∘ ⋯ ∘ Ψ_{P̂}(P_1))(1)) = χ(P̂)` on an above-diagonal `(aN, bN)`-path.

Two hypotheses are carried, and they are exactly the two things this file does not prove.

`hword` is the conclusion of the second, third and fourth paragraphs of the proof of
`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar`: the scalar-free sweep
word and the word `Ξ_{P̂', S(P̂)}` of `HJO.Sweep.markedWordOp` agree *at the vacuum* — not as
operators, the transport `Y_k` of `HJO.Sweep.transport` intervening at every intermediate index and
only returning to the identity at the end.

`hcor46` is `HJO.Mellit.map_constantCoeff_markedWordOp'`, which is not proved here: for a square
Dyck path `π` of length `n ≥ 1` and a marking `T ⊆ c(π)`, `ι(Ξ_{π,T}(1)) = χ(π, T)`. It is stated
in the general form so that a proof of `HJO.Mellit.map_constantCoeff_markedWordOp'` discharges it
verbatim, and it is applied at exactly one instance, `π = P̂' = HJO.Mellit.partnerPath y` and
`T = S(P̂) = HJO.Mellit.markedPositions y`, whose two side conditions are supplied here by
`HJO.Dyck.isSquareDyck_and_attackSet_eq_of_isTransitiveAttackSet`
(`HJO.Mellit.isSquareDyck_partnerPath`) and
`HJO.Paths.attackPartner_stepIndex_and_mem_corner_of_mem_sweepMarked`
(`HJO.Mellit.markedPositions_subset_corner`).

The first paragraph of the proof — that the two characteristic functions agree — is
`HJO.Mellit.sweepChar_eq_pathMarkedCharSeries`, proved above with no hypothesis. -/
theorem map_constantCoeff_psiWord_eq_sweepChar_of_cor46 (q : L) {y : Heights a b N}
    (hy : IsAboveDiagonal y) {ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L}
    (hword : psiWord q y (1 : Total L)
      = Sweep.markedWordOp q (partnerPath y) (markedPositions y) (1 : Total L))
    (hcor46 : ∀ {n : ℕ} (x : Fin n → ℕ) (T : Finset (ℕ × ℕ)), 1 ≤ n → Dyck.IsSquareDyck n x →
      T ⊆ Dyck.corner x →
      ι (MvPolynomial.constantCoeff (Sweep.markedWordOp q x T (1 : Total L)))
        = Dyck.pathMarkedCharSeries q x T) :
    ι (MvPolynomial.constantCoeff (psiWord q y (1 : Total L))) = sweepChar q y := by
  rcases Nat.eq_zero_or_pos (b * N) with h0 | h0
  · rw [hword, markedWordOp_eq_one_of_eq_zero q h0, Module.End.one_apply, map_one, map_one,
      sweepChar_eq_pathMarkedCharSeries q hy, Dyck.pathMarkedCharSeries,
      markedCharSeries_eq_one_of_eq_zero q h0]
  · rw [hword, hcor46 _ _ h0 (isSquareDyck_partnerPath hy) (markedPositions_subset_corner hy),
      sweepChar_eq_pathMarkedCharSeries q hy]

/-! ### `HJO.Mellit.sweepComputes` modulo `HJO.Mellit.map_constantCoeff_markedWordOp'` -/

/-- **`HJO.Mellit.SweepComputes` from the second conjunct of
`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar`.** The named `Prop` that
`HJO.Mellit.shuffle_of_three` asks for, reduced to the identity `ι(Ψ(P̂)(1)) = χ(P̂)` of
`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar` at every above-diagonal
path of the rectangle.

`q ≠ 0` is what collecting the scalars costs; every consumer has it, `shuffle_of_three` asking for
`SweepComputes` only under `AlgebraicIndependent ℤ ![q, u]`. -/
theorem sweepComputes_of_charWord (q u : L) (hq : q ≠ 0)
    (hcw : ∀ (M : ℕ) (y : Heights a b M), IsAboveDiagonal y →
      ∀ ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L, Sym.IsRealisation ι →
        ι (MvPolynomial.constantCoeff (psiWord q y (1 : Total L))) = sweepChar q y) :
    SweepComputes q u a b := by
  intro ι hι M y hy
  rw [sweepWord_eq_smul_psiWord_of_isAboveDiagonal q u hq hy, LinearMap.smul_apply,
    MvPolynomial.constantCoeff_smul, map_smul, hcw M y hy ι hι]

/-- **`HJO.Mellit.SweepComputes` modulo `HJO.Mellit.map_constantCoeff_markedWordOp'` and the
identification of the two words.** The composite of everything above: with `hword` — the second,
third and fourth paragraphs of the proof of
`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar` — and
`HJO.Mellit.map_constantCoeff_markedWordOp'`, the last link of the sweep leg of
`HJO.Mellit.shuffle_of_three` is a theorem.

Nothing else is open on this leg: the first paragraph of
`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar` is
`HJO.Mellit.sweepChar_eq_pathMarkedCharSeries`, the collection of the scalars is
`HJO.Mellit.sweepWord_eq_smul_psiWord`, and the two exponents are
`HJO.Paths.card_filter_eventType_E` and
`HJO.Paths.sum_sweepRight_D_sub_sum_sweepRight_C_eq_aboveHookCount_sub_aboveMaxTdinv`, all
proved. -/
theorem sweepComputes_of_cor46 (q u : L) (hq : q ≠ 0)
    (hword : ∀ (M : ℕ) (y : Heights a b M), IsAboveDiagonal y →
      psiWord q y (1 : Total L)
        = Sweep.markedWordOp q (partnerPath y) (markedPositions y) (1 : Total L))
    (hcor46 : ∀ ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L, Sym.IsRealisation ι →
      ∀ {n : ℕ} (x : Fin n → ℕ) (T : Finset (ℕ × ℕ)), 1 ≤ n → Dyck.IsSquareDyck n x →
        T ⊆ Dyck.corner x →
        ι (MvPolynomial.constantCoeff (Sweep.markedWordOp q x T (1 : Total L)))
          = Dyck.pathMarkedCharSeries q x T) :
    SweepComputes q u a b :=
  sweepComputes_of_charWord q u hq fun M y hy ι hι =>
    map_constantCoeff_psiWord_eq_sweepChar_of_cor46 q hy (hword M y hy) (hcor46 ι hι)

/-! ### The degree -/

/-- **The fifth paragraph of the proof of
`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar`: the degree.** Once
`ι(f) = χ(P̂)` is known, `f` is homogeneous of degree `bN`, with no further input from the sweep.

`χ(P̂)` is a sum of monomials `x_{w_1} ⋯ x_{w_{bN}}`, hence supported in total degree `bN`; and a
symmetric function whose realisation is supported in one total degree lies in that graded piece, by
`HJO.Sym.mem_lambdaComp_of_coeff_iota` — which is the argument through
`HJO.Sym.lambdaComp_isInternal` and `HJO.Sym.realisation_injective`, already packaged. -/
theorem constantCoeff_psiWord_one_mem_lambdaComp_of_map_eq_sweepChar (q : L)
    {y : Heights a b N} (hy : IsAboveDiagonal y)
    {ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L} (hι : Sym.IsRealisation ι)
    (h : ι (MvPolynomial.constantCoeff (psiWord q y (1 : Total L))) = sweepChar q y) :
    MvPolynomial.constantCoeff (psiWord q y (1 : Total L)) ∈ Sym.LambdaComp L (b * N) := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  refine Sym.mem_lambdaComp_of_coeff_iota hι fun α hα => ?_
  by_contra hne
  rw [h, sweepChar_eq_pathMarkedCharSeries q hy, Dyck.pathMarkedCharSeries] at hα
  refine hα (Dyck.coeff_markedCharSeries_eq_zero_of_sum_ne ?_)
  rw [Finsupp.sum]
  exact hne

/-- **`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar` modulo
`HJO.Mellit.map_constantCoeff_markedWordOp'` and the identification of the two words.** The whole of
the lemma in the encoding `HJO.Mellit.sweepComputes` uses: the element
`f = (Ψ_{P̂}(P_M) ∘ ⋯ ∘ Ψ_{P̂}(P_1))(1)` of `Λ` is homogeneous of degree `bN` and every realisation
carries it to `χ(P̂)`.

The two hypotheses are those of `HJO.Mellit.map_constantCoeff_psiWord_eq_sweepChar_of_cor46`; see
its docstring for what each is and why it is open. **This is not an unconditional proof of the
lemma**, `hword` and `hcor46` both being open. -/
theorem constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar_of_cor46 (q : L)
    {y : Heights a b N} (hy : IsAboveDiagonal y)
    {ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L} (hι : Sym.IsRealisation ι)
    (hword : psiWord q y (1 : Total L)
      = Sweep.markedWordOp q (partnerPath y) (markedPositions y) (1 : Total L))
    (hcor46 : ∀ {n : ℕ} (x : Fin n → ℕ) (T : Finset (ℕ × ℕ)), 1 ≤ n → Dyck.IsSquareDyck n x →
      T ⊆ Dyck.corner x →
      ι (MvPolynomial.constantCoeff (Sweep.markedWordOp q x T (1 : Total L)))
        = Dyck.pathMarkedCharSeries q x T) :
    MvPolynomial.constantCoeff (psiWord q y (1 : Total L)) ∈ Sym.LambdaComp L (b * N) ∧
      ι (MvPolynomial.constantCoeff (psiWord q y (1 : Total L))) = sweepChar q y :=
  have h := map_constantCoeff_psiWord_eq_sweepChar_of_cor46 q hy hword hcor46
  ⟨constantCoeff_psiWord_one_mem_lambdaComp_of_map_eq_sweepChar q hy hι h, h⟩

/-- **`HJO.Mellit.sweepComputes` modulo `HJO.Mellit.map_constantCoeff_markedWordOp'` and the
identification of the two words.** The statement: for an above-diagonal
`(aN, bN)`-path `y` and a realisation `ι`, the element
`f = W(P̂)(1)` of `Λ` is homogeneous of degree `bN` and
`ι(f) = u^{ârea(P̂)} q^{ĥ(P̂) - max t̂dinv(P̂)} χ(P̂)`.

**This is not an unconditional proof of `HJO.Mellit.sweepComputes`**: `hword` and `hcor46` are
both open. -/
theorem constantCoeff_sweepWord_one_mem_lambdaComp_and_map_eq_smul_sweepChar_of_cor46 (q u : L)
    (hq : q ≠ 0) {y : Heights a b N} (hy : IsAboveDiagonal y)
    {ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L} (hι : Sym.IsRealisation ι)
    (hword : psiWord q y (1 : Total L)
      = Sweep.markedWordOp q (partnerPath y) (markedPositions y) (1 : Total L))
    (hcor46 : ∀ {n : ℕ} (x : Fin n → ℕ) (T : Finset (ℕ × ℕ)), 1 ≤ n → Dyck.IsSquareDyck n x →
      T ⊆ Dyck.corner x →
      ι (MvPolynomial.constantCoeff (Sweep.markedWordOp q x T (1 : Total L)))
        = Dyck.pathMarkedCharSeries q x T) :
    MvPolynomial.constantCoeff (sweepWord q u y (1 : Total L)) ∈ Sym.LambdaComp L (b * N) ∧
      ι (MvPolynomial.constantCoeff (sweepWord q u y (1 : Total L))) =
        (u ^ aboveArea y * q ^ ((aboveHookCount y : ℤ) - (aboveMaxTdinv y : ℤ))) •
          sweepChar q y :=
  constantCoeff_sweepWord_one_mem_lambdaComp_and_map_eq_smul_sweepChar_of_charWord q u hq hy
    (constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar_of_cor46 q hy hι hword hcor46)

end HJO.Mellit
