/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepWitnessAppend
public import HJO.Shuffle.SweepWitnessColour

/-! # `LhsRewrite` at the sweep witness is one identity, and the replication family is gone

`HJO.Mellit.MellitInput` asks for a `HJO.Mellit.SweepSystem` satisfying four clauses.
`HJO.Mellit.sweepWitness` is that system, and the clauses reduce at it one at a time:
`RhsSumsAgree` outright (`rhsSumsAgree_sweepWitness`), `Rem41` down to `SweepComputes`
(`rem41_of_sweepComputes` with its `hD` supplied by `sweepWitness_proj_dminus_pow_D`), and
`MellitInduction` down to `SweepAppend` as an equivalence
(`mellitInduction_sweepWitness_iff_sweepAppend`). This file does the fourth,
`HJO.Mellit.LhsRewrite`.

## What is removed, and what is left

`LhsRewrite` quantifies over a realisation `ι`, a slope homomorphism `Θ`, AND a replication family
`Ω`, and its right-hand side reads `S.proj (S.dminus^ℓ (stageWord S Ω a b α))` -- three layers of
structure around the object of interest. At this witness all three collapse:

* the stage acts degreewise, by `HJO.Mellit.sweepWitness_stage_sweepIn`, so the stage word is
  `HJO.Mellit.stageWordTotal` -- a word in the sweep operators (`trainDownEnd`, `trainUpEnd`,
  `slopeOperator`, `zopOneStar`, `dplusStar`, multiplication by `y_1`) with **no `Ω` in it**;
* `d_-^ℓ` on the grading `ℓ` is `HJO.Sweep.lowerRun q ℓ`, by `HJO.Mellit.gradedOp_dminus_pow`,
  reading the indices `ℓ, ℓ-1, …, 1` and landing on the grading `0`;
* `proj` there is the constant coefficient, by `HJO.Mellit.sweepWitness_proj_gradedIn`.

`HJO.Mellit.sweepWitness_proj_dminus_pow_stageWord` is the composite, and the point of it is that
its right-hand side does not mention `Ω`: every replication family gives the same value. That is
what makes `HJO.Mellit.lhsRewrite_sweepWitness_iff_lhsComputes` an EQUIVALENCE rather than a
one-way reduction -- the `∀ Ω` in `LhsRewrite` is not weakened away, it is discharged, because
`HJO.Mellit.replExists` supplies one family and the value is independent of which.

What remains, `HJO.Mellit.LhsComputes`, is Mellit's Section 3.7 with nothing structural left around
it: for every realisation and every slope homomorphism,
`(-1)^{N(b+1)} ι(Θ(C_α 1) 1)
  = (-1)^{(a-1)N} q^{ℓ-N} ι(constantCoeff(lowerRun q ℓ (stageWordTotal α)))`.

## What this does NOT do

It does not prove `HJO.Mellit.lhsRewrite_sweepWitness`. The identity above is
still the substance of Mellit's Section 3.7: it equates the slope-operator side, which is what the
compositional shuffle identity is stated in, with a concrete word in the Carlsson--Mellit operators,
and nothing here touches that bridge. What is proved is the field at this witness, which is a
different statement from `HJO.Mellit.lhsRewrite_sweepWitness`.

What the reduction buys is that the remaining work is stated about concrete objects instead of
about an abstract structure with an existentially quantified family inside it. It does NOT make
the remaining work small: there is no short route, as explained below.

## There is no direct route to `LhsComputes`, measured

`HJO/Shuffle/SweepWitnessLhsSingleton.lean` settles this, and its conclusion is negative:
`LhsComputes` is a CROSS-ALGEBRA BRIDGE ALREADY AT `N = 1`, so no induction on `α` can avoid the
Section 3.7 cone.

There is no `α = []` corner, because the clause requires `0 < N`. The smallest instance is
`α = (1)`, and there everything except the bridge discharges: `C_1(1) = h_1 = e_1 = -U_1`, so the
`k = 1` prescription of `HJO.Sym.IsSlopeHom` pins `Θ` on the seed by itself
(`HJO.Mellit.theta_copComp_one`), and the clause reduces to

`(-1)^b ι(Q_{a,b} 1) = (-1)^{a-1} ι(constantCoeff(lowerRun q 1 (stageWordTotal q u a b [1])))`

(`HJO.Mellit.qop_apply_one_of_lhsComputes`). The left side lives in
`Module.End L (HJO.Sym.Lambda L)` as nested commutators of `HJO.Sym.Dop`; the right lives in
`HJO.Sweep.Total L` as a word in `slopeOperator`, `dplusStar` and `trainDownEnd`. The `a = 1`
sub-corner does not help -- it collapses the left to `(-1)^b e_b` while the right still carries a
nonempty word in `-y_1` and `(qu)^{-1}z_1`.

Two facts qualify this conclusion without overturning it.

* The gap is not total. `HJO.Sweep.dop_one_eq_neg_dminusCM_dplusStar`
  (`HJO/CarlssonMellit/DopFromDplusStar.lean`) is a
  proved cross-algebra identity carrying no hypothesis on `q` or `u`:
  `C(D_1 f) = -d_-(d^*_+(C f))`. The *shape* of the bridge is therefore present and proved; what is
  absent is its general `D_n`, and with it `Q_{a,b}`.
* The Section 3.7 inputs are proved: `HJO.Sweep.exists_slopeActions`
  (`HJO/Shuffle/SlopeActions.lean`), `HJO.Mellit.map_constantCoeff_markedWordOp'`
  (`HJO/CarlssonMellit/LoweringSumClosed.lean`) and `HJO.Dyck.Tilde.rel_biHomogeneous`, as
  `HJO.Dyck.Tilde.Atilde.biGrading` (`HJO/CarlssonMellit/BiGraded.lean`).

That those results are proved does not make the bridge available, and this is the point that
matters: NEITHER of their statements mentions `HJO.Sym.Qop` or `HJO.Sym.Dop`.
`exists_slopeActions` produces families of algebra maps `Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)`;
`map_constantCoeff_markedWordOp'` equates `ι(constantCoeff(markedWordOp q x T 1))` with
`Dyck.pathMarkedCharSeries q x T`. Both live entirely inside the Carlsson--Mellit layer. So the
statement that carries `Θ(C_α 1)` out of `Module.End L (Lambda L)` is still unnamed and unstated,
and it -- not the proved inputs -- is what the base case costs.

The structural contrast with the `SweepAppend` precedent is the point, and it explains why that
reduction was cheap and this one cannot be. `MellitInduction` reduced without the braid layer
because BOTH ITS SIDES ARE WORDS IN THE SAME OPERATORS. Here they are objects of two different
algebras, and `HJO.Mellit.mellitInduction_sweepWitness` -- available as `SweepAppend` -- only
propagates the identity along `α`; it cannot supply the base case.

## A degenerate regime lives inside this statement

`LhsComputes` carries no hypothesis on `q` or `u`, and at `q u ∈ {0, 1}` it says something else.
`HJO.Sym.axisGen` carries the scalar `v/(v-1)`, which vanishes at `v = 0` and -- since Lean's `1/0`
is `0` -- also at `v = 1`, so every axis generator is zero (`HJO.Sym.axisGen_eq_zero`). `IsSlopeHom`
then degenerates to the `Θ`-free condition `∀ k ≥ 1, Q_{ak,bk} = 0`
(`HJO.Sym.isSlopeHom_iff_of_degenerate`), the constant-term homomorphism `HJO.Sym.constHom` is a
slope homomorphism there, and it kills the creation seed -- collapsing the clause to the vanishing
of its own right-hand side (`HJO.Mellit.lhsComputes_rhs_eq_zero_of_degenerate`).

This does not damage the equivalence below: `LhsRewrite` quantifies over `Θ` identically, so both
`Prop`s degenerate together and the `iff` is unaffected. But any proof of `LhsComputes` has to
dispose of that regime, and `MellitInput`'s own quantifier is generic
(`AlgebraicIndependent ℤ ![q, u]`), so the obligation is an artefact of stating the residual more
generally than its one consumer needs rather than mathematics anybody wants.

**That regime is settled negatively: `LhsComputes` as stated is FALSE.**
`HJO/Shuffle/SweepWitnessLhsRefuted.lean` refutes it at `(q, u) = (1,1)`, `(0,1)` and `(1,0)`
for every `1 < a` (`HJO.Mellit.not_lhsComputes_of_degenerate`), and with it the `LhsRewrite` clause
at this witness (`HJO.Mellit.not_lhsRewrite_sweepWitness_of_degenerate`) -- through the equivalence
below, which carries no hypothesis on `q` or `u` either. The sharp form
`HJO.Mellit.lhsComputes_iff_of_degenerate` shows the clause is true at `qu ∈ {0,1}` exactly when it
is vacuous, so the obligation above has only one discharge: the degenerate regime must be excluded
by hypothesis, and the genericity has to be threaded into the residual's own statement. No route can
prove the `Prop` as written.

The sign, by contrast, is correct as stated, and `0 < a` is what makes it so:
`HJO.Mellit.neg_one_pow_bigrading` proves `(-1)^{N(b+1)}(-1)^{N(a+b)} = (-1)^{(a-1)N}` over `ℕ`
with truncated subtraction, the exponents differing by `2N`. At `a = 0` truncation gives
`(a-1)N = 0` while the bigrading gives `(-1)^N`, and they disagree at odd `N`
(`neg_one_pow_bigrading_ne_of_a_eq_zero`). The equivalence below carries `0 < a`, so nothing
downstream reads that corner.

## Generality

No hypothesis on `q` or `u`; `Nat.Coprime a b`, `0 < a` and `0 < b` only, and those only because
`sweepWitness_stage_sweepIn` needs them to evaluate `Ω` through the Stern--Brocot recursion. In
particular nothing here spends the genericity that `MellitInput` carries, and nothing here is
affected by the `α = [0]` corner that the `colourParts` convention has: `stageWordTotal` is defined
by recursion on the list and reads no colouring.
-/

@[expose] public section

namespace HJO.Mellit

open HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {a b : ℕ}

/-! ### The stage word as a word in the sweep operators -/

/-- **`G_{ℓ,α_ℓ} ⋯ G_{1,α_1}` at the witness, applied from the grading `k`.** The mirror of
`HJO.Mellit.stageFrom` with `HJO.Mellit.stage` replaced by `HJO.Mellit.stageTotal`, so that no
sweep system and no replication family occurs. Each letter raises the grading by one, which is why
the index is carried explicitly: the stage at grading `k` is a different operator from the stage at
grading `k + 1`. -/
noncomputable def stageFromTotal (q u : L) (a b : ℕ) : ℕ → Total L → List ℕ → Total L
  | _, F, [] => F
  | k, F, A :: α => stageFromTotal q u a b (k + 1) (stageTotal q u a b k A F) α

/-- **`G_{ℓ,α_ℓ} ⋯ G_{1,α_1}(1)` at the witness**, the element of the grading `ℓ` that
`HJO.Mellit.lhsRewrite_sweepWitness` and `HJO.Mellit.mellitInduction_sweepWitness` both name, as a
word in the sweep operators applied to the unit. -/
noncomputable def stageWordTotal (q u : L) (a b : ℕ) (α : List ℕ) : Total L :=
  stageFromTotal q u a b 0 1 α

/-- **The stage word acts degreewise, from any grading.** Induction on the composition, one
application of `HJO.Mellit.sweepWitness_stage_sweepIn` per letter. -/
theorem sweepWitness_stageFrom_sweepIn (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {Ω : ℕ → ℕ → ℕ → ((sweepWitness q u a b).W →ₗ[L] (sweepWitness q u a b).W)}
    (hΩ : IsReplicationFamily (sweepWitness q u a b) Ω) (α : List ℕ) (k : ℕ) (F : Total L) :
    stageFrom (sweepWitness q u a b) Ω a b k (sweepIn q u a b k F) α
      = sweepIn q u a b (k + α.length) (stageFromTotal q u a b k F α) := by
  induction α generalizing k F with
  | nil => rfl
  | cons A α ih =>
      rw [stageFrom, sweepWitness_stage_sweepIn hab ha hb hΩ, ih, stageFromTotal,
        show k + 1 + α.length = k + (A :: α).length by rw [List.length_cons]; omega]

/-- **The stage word at the witness is `HJO.Mellit.stageWordTotal` in the grading `ℓ`.** The vacuum
is the unit of the grading `0` (`HJO.Mellit.sweepIn_zero_one`), and the run from there consumes the
composition. -/
theorem sweepWitness_stageWord_sweepIn (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {Ω : ℕ → ℕ → ℕ → ((sweepWitness q u a b).W →ₗ[L] (sweepWitness q u a b).W)}
    (hΩ : IsReplicationFamily (sweepWitness q u a b) Ω) (α : List ℕ) :
    stageWord (sweepWitness q u a b) Ω a b α
      = sweepIn q u a b α.length (stageWordTotal q u a b α) := by
  rw [stageWord, ← sweepIn_zero_one q u a b,
    sweepWitness_stageFrom_sweepIn hab ha hb hΩ, stageWordTotal, Nat.zero_add]

/-- **The right-hand side of `LhsRewrite` at the witness, with the replication family gone.**
`proj (d_-^ℓ (G_ℓ ⋯ G_1(1))) = constantCoeff (lowerRun q ℓ (stageWordTotal α))`.

The right-hand side does not mention `Ω`. That is the content: `LhsRewrite` quantifies over every
replication family, and at this witness they all give the same value, so the quantifier can be
discharged from `HJO.Mellit.replExists` rather than assumed. -/
theorem sweepWitness_proj_dminus_pow_stageWord (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {Ω : ℕ → ℕ → ℕ → ((sweepWitness q u a b).W →ₗ[L] (sweepWitness q u a b).W)}
    (hΩ : IsReplicationFamily (sweepWitness q u a b) Ω) (α : List ℕ) :
    (sweepWitness q u a b).proj
        (((sweepWitness q u a b).dminus ^ α.length) (stageWord (sweepWitness q u a b) Ω a b α))
      = MvPolynomial.constantCoeff (lowerRun q α.length (stageWordTotal q u a b α)) := by
  rw [sweepWitness_stageWord_sweepIn hab ha hb hΩ]
  change (sweepWitness q u a b).proj
      (((gradedOp (fun k => dminus q k) (fun k => k - 1)) ^ α.length)
        (gradedIn L α.length (stageWordTotal q u a b α))) = _
  rw [gradedOp_dminus_pow, sweepWitness_proj_gradedIn]

/-! ### The residual identity -/

/-- **What `LhsRewrite` costs at the sweep witness.** Mellit's Section 3.7 with no sweep system, no
replication family and no projection left in it: for every realisation `ι` and every slope
homomorphism `Θ`, and every composition `α` of `N` with positive parts,

`(-1)^{N(b+1)} ι(Θ(C_α 1) 1)
  = (-1)^{(a-1)N} q^{ℓ-N} ι(constantCoeff(lowerRun q ℓ (stageWordTotal α)))`.

Both sides are elements of `HJO.Sym.AlphabetSeries L`. The left is the slope-operator side, which is
what the compositional rational shuffle identity is stated in; the right is a concrete word in the
Carlsson--Mellit operators, run down through `d_-` and read at the constant coefficient. -/
def LhsComputes (q u : L) (a b : ℕ) : Prop :=
  ∀ (ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L), Sym.IsRealisation ι →
    ∀ Θ : Sym.Lambda L →ₐ[L] Module.End L (Sym.Lambda L), Sym.IsSlopeHom a b q u Θ →
      ∀ N : ℕ, 0 < N → ∀ α : List ℕ, (∀ x ∈ α, 0 < x) → α.sum = N →
        (-1 : L) ^ (N * (b + 1)) • ι (Θ (Sym.CopComp q α 1) 1)
          = ((-1 : L) ^ ((a - 1) * N) * q ^ ((α.length : ℤ) - (N : ℤ))) •
              ι (MvPolynomial.constantCoeff (lowerRun q α.length (stageWordTotal q u a b α)))

/-- **`LhsRewrite` at the sweep witness is exactly `HJO.Mellit.LhsComputes`.**

An equivalence, not a one-way reduction. The forward direction instantiates the clause's `∀ Ω` at
the family `HJO.Mellit.replExists` produces; the backward direction serves an arbitrary `Ω`, which
is legitimate because `HJO.Mellit.sweepWitness_proj_dminus_pow_stageWord` shows the value the clause
asserts does not depend on the family. So nothing is weakened in either direction, and in particular
the reverse direction certifies that the residual is not satisfiable by fiat any more than the
clause already was. -/
theorem lhsRewrite_sweepWitness_iff_lhsComputes (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) :
    LhsRewrite (sweepWitness q u a b) a b ↔ LhsComputes q u a b := by
  constructor
  · intro h ι hι Θ hΘ N hN α hpos hsum
    obtain ⟨Ω, hΩ⟩ := replExists (sweepWitness q u a b)
    rw [← sweepWitness_proj_dminus_pow_stageWord hab ha hb hΩ]
    exact h ι hι Θ hΘ Ω hΩ N hN α hpos hsum
  · intro h ι hι Θ hΘ Ω hΩ N hN α hpos hsum
    rw [sweepWitness_proj_dminus_pow_stageWord hab ha hb hΩ]
    exact h ι hι Θ hΘ N hN α hpos hsum

end HJO.Mellit
