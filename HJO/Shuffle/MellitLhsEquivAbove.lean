/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepComputesClosed
public import HJO.Shuffle.MellitAssembly
public import HJO.Shuffle.GesselReversal
public meta import HJO.Attr

/-! # `LhsComputes` given `MellitInduction` is EQUIVALENT to `ShuffleAbove`

The proof of `HJO.Mellit.lhsRewrite_sweepWitness` cites `HJO.Mellit.mellitInduction_sweepWitness`,
and almost all of its other inputs are proved independently, so one might expect the shuffle side
to collapse to a single `Prop` once those inputs are composed.

**This file measures what the composition costs, and the answer is that it costs the theorem.**
Modulo results proved elsewhere, `HJO.Mellit.LhsComputes` *given*
`HJO.Mellit.MellitInduction` is not a corollary of it: the two are **equivalent** to
`HJO.ShuffleAbove`, `HJO.shuffleAbove`, which is the deep content of the shuffle
side and the immediate predecessor of the main theorem. So the two `Prop`s `LhsComputes` and
`MellitInduction` are indeed not independent, but there is no bookkeeping step here to write.
Deriving `LhsComputes` from `MellitInduction` and deriving `ShuffleAbove` from `MellitInduction`
are the same task.

## Why, in one line

Three of the four clauses of `HJO.Mellit.MellitInput` are theorems at
`HJO.Mellit.sweepWitness`, and between them they already compute the **right-hand side** of
`LhsComputes`:

* `HJO.Mellit.rhsSumsAgree_sweepWitness` is `RhsSumsAgree` outright;
* `HJO.Mellit.rem41_of_sweepComputes` reduces `Rem41` to `HJO.Mellit.SweepComputes`, and that is now
  a theorem (`HJO.Mellit.sweepComputes_of_algebraicIndependent`);
* `HJO.Mellit.sweepWitness_proj_dminus_pow_stageWord` erases the replication family from the stage
  word.

`Rem41` and `RhsSumsAgree` together say that `u^{N-ℓ} d_-^ℓ D_{η,c_α}` is the sum over
above-diagonal parking functions, and `MellitInduction` turns `D_{η,c_α}` into the stage word. So
`MellitInduction` **pins the right-hand side of `LhsComputes` to the parking-function sum** — that
is `HJO.Mellit.smul_constantCoeff_lowerRun_stageWordTotal_eq_aboveSum` below, and it is exactly the
`hX`/`hscal` computation inside `HJO.Mellit.aboveIdentity_of_mellit` with the appeal to `LhsRewrite`
deleted. What is then left of `LhsComputes` is its left-hand side against that sum, and that is
`ShuffleAbove` verbatim.

## What this does and does not say about the proof of `HJO.Mellit.lhsRewrite_sweepWitness`

It does **not** refute a step of that proof, nor is it wrong to cite
`HJO.Mellit.mellitInduction_sweepWitness`. What the file locates is the step that carries the
content: the transport of the base action to
the replicated one at `(a,b)`, carrying `Θ(C_α 1)` to the corresponding element of the
`(a,b)`-graded piece. The results cited *around* that step are proved, and the step itself is a
bridge between two worlds: `HJO.Sym.Qop`, which lives on `Λ = HJO.Sym.Lambda L`, and the replicated
actions of `HJO.Sweep.exists_slopeActions`, which live on `HJO.Sweep.Vstar L`.
`HJO/Shuffle/MellitLhsSlopeBase.lean` states the general-slope form of that bridge,

`C(Q_{a,b}f) = (-1)^{b+1} d_-(Ξ^{(1)}_{a,b}(y_1 d^*_+(Cf)))`   for coprime `a, b ≥ 1`,

and names what it needs (`HJO.Sweep.zopOneStar_one_auxVar_sq`: an evaluation of
`HJO.Sweep.zopOneStar q u 1` on a general element of `V_1`). So the inputs around that step being
proved and "the composition is the theorem" are both true: the inputs a proof cites do not measure
the transport it performs between them.

The same phenomenon — a step that looks like a reduction and is a restatement of its own
conclusion — occurs for the mediant induction (`HJO.Mellit.nTermGlue_iff_lhsSlope`). Here it is an
equivalence with `HJO.ShuffleAbove` itself rather than with a local clause.

## Genericity

`AlgebraicIndependent ℤ ![q, u]` is spent and nothing else is: `q ≠ 0` for
`HJO.Mellit.rhsSumsAgree_sweepWitness`, `u ≠ 0` for the cancellation
`q^{ℓ-N} = u^{N-ℓ}(qu)^{ℓ-N}`, and `q ≠ 0`, `q ≠ 1`, `∀ r, IsUnit (q^{r+1}-1)` for
`HJO.Mellit.sweepComputes_of_algebraicIndependent`. Both exclusions are real rather than artefacts:
at `u = 0` the scalar identity `hscal` below is false as an identity of `zpow`s, and `LhsComputes`
itself is refuted at `(q,u) = (1,1)`, `(0,1)` and `(1,0)` for every `1 < a`
(`HJO.Mellit.not_lhsComputes_of_qop_eq_zero`, `HJO.Mellit.not_lhsComputes_of_degenerate`). The
equivalence is stated at `0 < a` and `0 < b` rather than at `1 < a < b`, the narrower band being
needed by neither side.

## Implementation notes

The equivalence is not a step of the proof of the main theorem: it is a measurement of the distance
between `HJO.Mellit.LhsComputes` and `HJO.ShuffleAbove`.
-/

@[expose] public section

namespace HJO.Mellit

open HJO.Sweep HJO.ParkingFunctions HJO.Paths Finset

universe w

variable {L : Type w} [Field L] [Algebra ℚ L]

/-! ### Genericity -/

/-- `AlgebraicIndependent ℤ ![q, u]` forces `u ≠ 0`, the companion of
`HJO.Mellit.ne_zero_of_algebraicIndependent_fst` and the same step that
`HJO.Mellit.shuffleAbove_of_mellit` performs inline. -/
theorem ne_zero_of_algebraicIndependent_snd {K : Type*} [Field K] {q u : K}
    (hqu : AlgebraicIndependent ℤ ![q, u]) : u ≠ 0 := fun h0 => by
  have hz : (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℤ) = 0 :=
    PhiPoly.eq_of_aeval_eq hqu (by simp [h0])
  have hz' := congrArg (MvPolynomial.aeval ![(1 : ℤ), 1]) hz
  simp at hz'

/-! ### `Rem41` at the witness, with `SweepComputes` spent -/

/-- **`HJO.Mellit.Rem41` holds at `HJO.Mellit.sweepWitness`**, unconditionally at an algebraically
independent pair. This is `HJO.Mellit.rem41_of_sweepComputes` with all three of its hypotheses
discharged: `hchi` by `rfl`, since the witness takes `HJO.Paths.sweepChar` for its `χ`; `hD` by
`HJO.Mellit.sweepWitness_proj_dminus_pow_D`; and the clause itself by
`HJO.Mellit.sweepComputes_of_algebraicIndependent`.

`HJO.Mellit.mellitInput_of_three` assembles exactly this, but takes `SweepComputes` as a hypothesis
rather than spending the theorem, so the `Rem41` of the witness is nowhere stated on its own. It is
stated here because the equivalence below reads it twice. -/
theorem rem41_sweepWitness {q u : L} {a b : ℕ} (hqu : AlgebraicIndependent ℤ ![q, u])
    (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) :
    Rem41 (sweepWitness q u a b) a b :=
  rem41_of_sweepComputes _ hab ha hb (fun _ _ _ _ => rfl)
    (fun N η _α hpos hsum => sweepWitness_proj_dminus_pow_D q u ha hb N η hpos hsum)
    (sweepComputes_of_algebraicIndependent q u hqu a b)

/-! ### `MellitInduction` computes the right-hand side of `LhsComputes` -/

/-- **The right-hand side of `HJO.Mellit.LhsComputes` is the above-diagonal parking-function sum, as
soon as `MellitInduction` holds.** For every realisation `ι` and every composition `α` of `N > 0`
with positive parts,

`(-1)^{(a-1)N} q^{ℓ-N} ι(ct(d_-^ℓ G_{ℓ,α_ℓ} ⋯ G_{1,α_1}(1)))
  = ∑_{π̂} q^{d̂inv(π̂)} u^{ârea(P̂_π̂)} F_{bN, îdes(π̂)^{∨bN}}`.

No `Θ` and no slope homomorphism occurs: this is a statement about the *sweep* side alone, which is
the whole point. It is the `hX`/`hscal` half of `HJO.Mellit.aboveIdentity_of_mellit` with the appeal
to `LhsRewrite` removed — `MellitInduction` rewrites `d_-^ℓ` of the stage word as `d_-^ℓ D_{η,c_α}`
at the separating level `HJO.Mellit.sepLevel`, the two signs `(-1)^{(a-1)N}` cancelling and
`q^{ℓ-N}(qu)^{N-ℓ}` collapsing to `u^{N-ℓ}`; then `Rem41` carries that to the sum over
above-diagonal paths and `RhsSumsAgree` to the sum over parking functions.

The replication family is discharged rather than assumed, by `HJO.Mellit.replExists` together with
`HJO.Mellit.sweepWitness_proj_dminus_pow_stageWord`, which is why no `Ω` appears. -/
theorem smul_constantCoeff_lowerRun_stageWordTotal_eq_aboveSum {q u : L} {a b : ℕ}
    (hqu : AlgebraicIndependent ℤ ![q, u]) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (hind : MellitInduction (sweepWitness q u a b) a b)
    (ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L) (hι : Sym.IsRealisation ι)
    (N : ℕ) (hN : 0 < N) (α : List ℕ) (hpos : ∀ x ∈ α, 0 < x) (hsum : α.sum = N) :
    ((-1 : L) ^ ((a - 1) * N) * q ^ ((α.length : ℤ) - (N : ℤ))) •
        ι (MvPolynomial.constantCoeff (lowerRun q α.length (stageWordTotal q u a b α)))
      = ∑ π ∈ aboveWithReturns α a b N,
          (q ^ aboveDinv π * u ^ aboveArea (abovePath π)) •
            gessel L (b * N) (descentReverse (b * N) (aboveIdes π)) := by
  obtain ⟨Ω, hΩ⟩ := replExists (sweepWitness q u a b)
  have hu : u ≠ 0 := ne_zero_of_algebraicIndependent_snd hqu
  have hq : q ≠ 0 := ne_zero_of_algebraicIndependent_fst hqu
  have hlevel : IsAdmissibleLevel (sepLevel a N) := isAdmissibleLevel_sepLevel a N
  have hsep : SeparatesDiagonal a b N (sepLevel a N) := separatesDiagonal_sepLevel hN
  have h2 := hind Ω hΩ N (sepLevel a N) hlevel hsep α hpos hsum
  have h3 := rem41_sweepWitness hqu hab ha hb ι hι N (sepLevel a N) hlevel hsep α hpos hsum
  have h4 := rhsSumsAgree_sweepWitness (q := q) (u := u) (a := a) (b := b) ha hq N hN α hpos hsum
  have hX : ι ((sweepWitness q u a b).proj
        (((sweepWitness q u a b).dminus ^ α.length)
          ((sweepWitness q u a b).D (sepLevel a N) (compColouring a b α))))
      = ((-1 : L) ^ ((a - 1) * N) * (q * u) ^ ((α.length : ℤ) - (N : ℤ))) •
          ι ((sweepWitness q u a b).proj
            (((sweepWitness q u a b).dminus ^ α.length)
              (stageWord (sweepWitness q u a b) Ω a b α))) := by
    rw [h2, map_smul, map_smul, map_smul]
  have hscal : ((-1 : L) ^ ((a - 1) * N) * q ^ ((α.length : ℤ) - (N : ℤ)))
      = u ^ ((N : ℤ) - (α.length : ℤ)) *
          ((-1 : L) ^ ((a - 1) * N) * (q * u) ^ ((α.length : ℤ) - (N : ℤ))) := by
    have hu1 : u ^ ((N : ℤ) - (α.length : ℤ)) * u ^ ((α.length : ℤ) - (N : ℤ)) = 1 := by
      rw [← zpow_add₀ hu]
      simp
    rw [mul_zpow]
    calc (-1 : L) ^ ((a - 1) * N) * q ^ ((α.length : ℤ) - (N : ℤ))
        = ((-1 : L) ^ ((a - 1) * N) * q ^ ((α.length : ℤ) - (N : ℤ)))
            * (u ^ ((N : ℤ) - (α.length : ℤ)) * u ^ ((α.length : ℤ) - (N : ℤ))) := by
          rw [hu1, mul_one]
      _ = _ := by ring
  rw [← sweepWitness_proj_dminus_pow_stageWord hab ha hb hΩ, hscal, ← smul_smul, ← hX, ← h3, h4]

/-! ### The equivalence -/

/-- **`HJO.Mellit.LhsComputes`, given `MellitInduction`, IS the above-diagonal identity.** An
equivalence, not a reduction in either direction: with `MellitInduction` in hand at the witness, the
clause

`(-1)^{N(b+1)} ι(Θ(C_α 1) 1) = (-1)^{(a-1)N} q^{ℓ-N} ι(ct(d_-^ℓ G_ℓ ⋯ G_1(1)))`

and the clause

`(-1)^{N(b+1)} ι(Θ(C_α 1) 1) = ∑_{π̂} q^{d̂inv(π̂)} u^{ârea(P̂_π̂)} F_{bN, îdes(π̂)^{∨bN}}`

have the same content, because
`HJO.Mellit.smul_constantCoeff_lowerRun_stageWordTotal_eq_aboveSum` identifies their two right-hand
sides. The second is `HJO.ShuffleAbove` at this `(a, b, q, u)` up to the reflection of the descent
sets, and `HJO.gesselReverseSum` removes that — see
`HJO.Mellit.forall_lhsComputes_iff_shuffleAbove`.

So no part of `LhsComputes` is discharged by assuming `MellitInduction`: what remains after
assuming it is the whole of `HJO.shuffleAbove`. -/
theorem lhsComputes_iff_aboveIdentity {q u : L} {a b : ℕ}
    (hqu : AlgebraicIndependent ℤ ![q, u]) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (hind : MellitInduction (sweepWitness q u a b) a b) :
    LhsComputes q u a b ↔
      ∀ (ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L), Sym.IsRealisation ι →
        ∀ Θ : Sym.Lambda L →ₐ[L] Module.End L (Sym.Lambda L), Sym.IsSlopeHom a b q u Θ →
          ∀ N : ℕ, 0 < N → ∀ α : List ℕ, (∀ x ∈ α, 0 < x) → α.sum = N →
            (-1 : L) ^ (N * (b + 1)) • ι (Θ (Sym.CopComp q α 1) 1)
              = ∑ π ∈ aboveWithReturns α a b N,
                  (q ^ aboveDinv π * u ^ aboveArea (abovePath π)) •
                    gessel L (b * N) (descentReverse (b * N) (aboveIdes π)) := by
  constructor
  · intro h ι hι Θ hΘ N hN α hpos hsum
    rw [h ι hι Θ hΘ N hN α hpos hsum]
    exact smul_constantCoeff_lowerRun_stageWordTotal_eq_aboveSum hqu hab ha hb hind ι hι N hN α
      hpos hsum
  · intro h ι hι Θ hΘ N hN α hpos hsum
    rw [h ι hι Θ hΘ N hN α hpos hsum]
    exact (smul_constantCoeff_lowerRun_stageWordTotal_eq_aboveSum hqu hab ha hb hind ι hι N hN α
      hpos hsum).symm

/-- **The global statement: modulo `MellitInduction`, `LhsComputes` and `HJO.ShuffleAbove`
are the same `Prop`.** Both sides are quantified exactly as
`HJO.Mellit.shuffle_of_lhs_and_induction` quantifies them, so the equivalence is usable there
without reshaping anything.

The forward direction is the existing route, `HJO.Mellit.shuffleAbove_of_mellit` on
`HJO.Mellit.mellitInput_of_three` with `SweepComputes` spent. The backward direction is
`HJO.Mellit.lhsComputes_iff_aboveIdentity` preceded by one application of `HJO.gesselReverseSum`,
which reflects the descent sets of `HJO.ShuffleAbove`'s sum into the ones the equivalence is stated
with.

**What this settles.** One might expect a composition deriving `LhsComputes` from `MellitInduction`
and the other proved inputs of `HJO.Mellit.lhsRewrite_sweepWitness` to collapse the shuffle side
from two `Prop`s to one. The collapse is real — `HJO.ShuffleAbove` together with
`HJO.gesselReverseSum` gives `HJO.External.Shuffle` by `HJO.shuffle_of_above`, so a single `Prop`
does suffice — but the composition is not a short step: by this theorem it *is*
`HJO.shuffleAbove`. Composing those inputs is not a task distinct from proving the shuffle
identity. -/
theorem forall_lhsComputes_iff_shuffleAbove
    (hind : ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ a b : ℕ, Nat.Coprime a b → 1 < a →
      a < b → MellitInduction (sweepWitness q u a b) a b) :
    (∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b →
        LhsComputes q u a b) ↔ ShuffleAbove L := by
  constructor
  · intro hlhs
    exact shuffleAbove_of_mellit (gesselReverseSum L)
      (mellitInput_of_three hlhs hind
        fun q u hqu a b _ _ _ => sweepComputes_of_algebraicIndependent q u hqu a b)
  · intro h q u hqu a b hab ha hb
    refine (lhsComputes_iff_aboveIdentity hqu hab (by omega) (by omega)
      (hind q u hqu a b hab ha hb)).2 ?_
    intro ι hι Θ hΘ N hN α hpos hsum
    have hf : ι ((-1 : L) ^ (N * (b + 1)) • Θ (Sym.CopComp q α 1) 1)
        = ∑ π ∈ aboveWithReturns α a b N,
            (q ^ aboveDinv π * u ^ aboveArea (abovePath π)) •
              gessel L (b * N) (aboveIdes π) := by
      rw [map_smul]
      exact h a b hab ha hb q u hqu ι hι Θ hΘ N hN α hpos hsum
    have hres := gesselReverseSum L ι hι (b * N) (AboveParkingFunction a b N)
      (aboveWithReturns α a b N) (fun π => q ^ aboveDinv π * u ^ aboveArea (abovePath π))
      (fun π => aboveIdes π) (fun π _ => aboveIdes_subset π) _ hf
    rw [map_smul] at hres
    exact hres

end HJO.Mellit

end
