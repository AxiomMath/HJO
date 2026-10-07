/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepComputesClosed
public meta import HJO.Attr

/-! # `HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc`, closed

The statement has two conjuncts of different natures: that `c_α` is an admissible colouring at a
separating level, and the identity
`∑_{P̂} u^{ârea(P̂)} q^{ĥ(P̂) - max t̂dinv(P̂)} χ(P̂) = ι(u^{N-ℓ} d_-^ℓ D_{η,c_α})`.

**The identity** is *reduced* to the single named `Prop` `HJO.Mellit.SweepComputes` by
`HJO.Mellit.rem41_of_sweepComputes`, and that `Prop` is a theorem —
`HJO.Mellit.sweepComputes` of `HJO/CarlssonMellit/LoweringSumClosed.lean`. What this file adds
is the identity in the statement's *own* shape rather than the abstract-system shape
`HJO.Mellit.Rem41`, so that no `SweepSystem` and no pinning hypotheses `hchi`, `hD` stand between
the statement and the concrete operators: `HJO.Mellit.sum_sweepChar_eq_smul_dsc_of_sweepComputes` is
the same three-line argument read off `HJO.Mellit.dsc_compColouring_eq_sum_partialSweepWord` and
`HJO.Mellit.sweepWord_vac_eq` directly.

**The admissibility conjunct** is not stated by `HJO.Mellit.Rem41`: the abstract clause holds it
as a hypothesis of the clause it belongs to, so the statement here is in this respect the stronger
one and this half is genuinely new. The witness is built here —
`HJO.Mellit.compWitness`, the path that rises to the top of a block on leaving its touch point,
height `b A_i` at every abscissa `r` with `a A_{i-1} < r ≤ a A_i`. It is defined not blockwise but
by the equivalent closed formula `ŷ_r = b · min{k ∈ {A_0, …, A_ℓ} : r ≤ a k}`, the same path: the
least partial sum whose abscissa has reached `r` is `A_i` exactly on `a A_{i-1} < r ≤ a A_i`. The
closed form is what makes the four clauses of `HJO.Paths.IsAboveDiagonal` one-liners — monotonicity
because the constraint set shrinks with `r`, and the diagonal bound `b r ≤ a ŷ_r` because
`r ≤ a · min{…}` *is* the defining constraint. Its returns are exactly the partial sums (`0 < b`
reads the height back), so `HJO.Mellit.colouring_eq_compColouring_iff` turns it into the colouring
statement.

## Main results

* `HJO.Mellit.isAdmissibleColouring_compColouring` — the admissibility conjunct, outright. It reads
  no scalars, no realisation and no genericity: `a`, `b`, `N`, `η`, `α` only.
* `HJO.Mellit.aboveReturnPaths_nonempty` — a corollary worth naming: the left-hand sum is
  never vacuous where the identity is asserted.
* `HJO.Mellit.sum_sweepChar_eq_smul_dsc_of_sweepComputes` — the identity from `SweepComputes`, in
  the statement's own shape.
* `HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc` — **the statement**, under the
  ambient genericity.

## The hypothesis on the scalars, and where it comes from

`HJO.Mellit.sweepComputes` is proved under three conditions on `q`: `q ≠ 0`,
`q ≠ 1` and `∀ r, IsUnit (q ^ (r + 1) - 1)`. The statement carries none, because the *ambient*
coefficient field is not an arbitrary one: it is `𝕜 := ℚ(q,u)`, the field of rational functions
over `ℚ` in two indeterminates, where all three are automatic.
So the three conditions are the standing hypothesis made explicit, not a hypothesis the
statement lacks — and that standing hypothesis is rendered throughout as
`AlgebraicIndependent ℤ ![q, u]`, the binder `HJO.Mellit.MellitInput` and
`HJO.Mellit.shuffle_of_three` carry for the same reason.

The main theorem therefore takes `AlgebraicIndependent ℤ ![q, u]`, and
`HJO.Mellit.sweepComputes_of_algebraicIndependent` discharges the three conditions from it. It
costs nothing where the theorem is used: `HJO.shuffleAbove` reaches it through
`HJO.Mellit.shuffle_of_lhs_and_induction`, which quantifies over exactly that binder. The sharper
form, under the three conditions themselves, is
`HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc_of_q`; the admissibility conjunct is
separated out precisely so that it is available with no condition on the scalars at all, at every
field and every `q`, `u`.

## References

The lemma `HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc`, whose proof's witness
path this file builds. Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*,
Remark 4.1.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### The prefix sums of a composition -/

/-- `0` is a prefix sum. -/
private theorem zero_mem_scanl (α : List ℕ) : 0 ∈ α.scanl (· + ·) 0 :=
  (mem_scanl_add_iff α 0 0).2 ⟨0, Nat.zero_le _, by simp⟩

/-- The total is a prefix sum. -/
private theorem sum_mem_scanl (α : List ℕ) : α.sum ∈ α.scanl (· + ·) 0 :=
  (mem_scanl_add_iff α 0 α.sum).2 ⟨α.length, le_rfl, by simp⟩

/-- A prefix sum is at most the total. -/
private theorem le_sum_of_mem_scanl {α : List ℕ} {k : ℕ} (hk : k ∈ α.scanl (· + ·) 0) :
    k ≤ α.sum := by
  obtain ⟨m, -, hm⟩ := (mem_scanl_add_iff α 0 k).1 hk
  have h : (α.take m).sum + (α.drop m).sum = α.sum := by
    rw [← List.sum_append, List.take_append_drop]
  omega

/-! ### The witness path of a composition

The `P̂_α`, the path that rises to the top of a block on leaving its touch point. -/

variable {α : List ℕ}

/-- The least prefix sum `k` of `α` whose abscissa `a k` has reached `r` — `0` if there is none.
On `a A_{i-1} < r ≤ a A_i` this is `A_i`, so `b ·` of it is the `P̂_α`. -/
noncomputable def compReach (a : ℕ) (α : List ℕ) (r : ℕ) : ℕ :=
  sInf {k | k ∈ α.scanl (· + ·) 0 ∧ r ≤ a * k}

private theorem compReach_nonempty (hsum : α.sum = N) {r : ℕ} (hr : r ≤ a * N) :
    {k | k ∈ α.scanl (· + ·) 0 ∧ r ≤ a * k}.Nonempty := by
  refine ⟨N, ?_, hr⟩
  rw [← hsum]
  exact sum_mem_scanl α

private theorem compReach_mem (hsum : α.sum = N) {r : ℕ} (hr : r ≤ a * N) :
    compReach a α r ∈ α.scanl (· + ·) 0 ∧ r ≤ a * compReach a α r :=
  Nat.sInf_mem (compReach_nonempty hsum hr)

private theorem compReach_le (hsum : α.sum = N) {r : ℕ} (hr : r ≤ a * N) :
    compReach a α r ≤ N := by
  have h := le_sum_of_mem_scanl (compReach_mem (a := a) hsum hr).1
  omega

private theorem compReach_le_of_mem {r k : ℕ} (hk : k ∈ α.scanl (· + ·) 0) (hrk : r ≤ a * k) :
    compReach a α r ≤ k :=
  Nat.sInf_le ⟨hk, hrk⟩

/-- The constraint set shrinks as `r` grows, so `compReach` is monotone: the path never comes
back down. -/
private theorem compReach_mono (hsum : α.sum = N) {r s : ℕ} (hrs : r ≤ s) (hs : s ≤ a * N) :
    compReach a α r ≤ compReach a α s :=
  compReach_le_of_mem (compReach_mem hsum hs).1 (hrs.trans (compReach_mem hsum hs).2)

private theorem compReach_zero : compReach a α 0 = 0 :=
  Nat.le_zero.1 (compReach_le_of_mem (zero_mem_scanl α) (Nat.zero_le _))

/-- At the abscissa of a prefix sum the path is exactly at that prefix sum: the returns of the
witness are the prefix sums and nothing else. -/
private theorem compReach_mul (ha : 0 < a) {k : ℕ} (hk : k ∈ α.scanl (· + ·) 0)
    (hsum : α.sum = N) (hkN : k ≤ N) : compReach a α (a * k) = k := by
  have hle := compReach_le_of_mem (a := a) hk (le_refl (a * k))
  have hge := (compReach_mem (a := a) hsum (Nat.mul_le_mul le_rfl hkN)).2
  have hk' : k ≤ compReach a α (a * k) := Nat.le_of_mul_le_mul_left hge ha
  omega

/-- **The witness path of a composition**, the `P̂_α`: height
`b · min{k ∈ {A_0, …, A_ℓ} : r ≤ a k}` at abscissa `r`, which is `b A_i` on
`a A_{i-1} < r ≤ a A_i`. The `min` with `N` is only so that the definition needs no hypothesis to
land in the rectangle; under `α.sum = N` it is inert (`HJO.Mellit.compReach_le`). -/
noncomputable def compWitness (a b N : ℕ) (α : List ℕ) : Heights a b N := fun r =>
  ⟨b * min (compReach a α (r : ℕ)) N,
    Nat.lt_succ_of_le (Nat.mul_le_mul le_rfl (min_le_right _ _))⟩

private theorem ht_compWitness {r : ℕ} (hr : r ≤ a * N) :
    ht (compWitness a b N α) r = b * min (compReach a α r) N :=
  ht_coe (compWitness a b N α) ⟨r, by omega⟩

private theorem ht_compWitness' (hsum : α.sum = N) {r : ℕ} (hr : r ≤ a * N) :
    ht (compWitness a b N α) r = b * compReach a α r := by
  rw [ht_compWitness hr, min_eq_left (compReach_le hsum hr)]

/-- **The witness lies weakly above the diagonal.** The diagonal bound `b r ≤ a ŷ_r` is the
defining constraint `r ≤ a · compReach a α r` multiplied by `b`; monotonicity is
`HJO.Mellit.compReach_mono`; the two endpoints are `compReach a α 0 = 0` and
`compReach a α (aN) = N`. -/
theorem isAboveDiagonal_compWitness (ha : 0 < a) (hsum : α.sum = N) :
    IsAboveDiagonal (compWitness a b N α) := by
  have hNmem : N ∈ α.scanl (· + ·) 0 := by rw [← hsum]; exact sum_mem_scanl α
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ht_compWitness' hsum (Nat.zero_le _), compReach_zero, Nat.mul_zero]
  · rw [ht_compWitness' hsum le_rfl, compReach_mul ha hNmem hsum le_rfl]
  · intro r hr
    rw [ht_compWitness' hsum (by omega), ht_compWitness' hsum (by omega)]
    exact Nat.mul_le_mul le_rfl (compReach_mono hsum (by omega) (by omega))
  · intro r hr
    rw [ht_compWitness' hsum hr, mul_left_comm]
    exact Nat.mul_le_mul le_rfl (compReach_mem hsum hr).2

/-- **The return composition of the witness is `α`.** The heights are read back by `0 < b`, and
`HJO.Mellit.compReach_mul` places a return at every prefix sum; there is no other return because
`compReach a α (a k)` is itself a prefix sum. -/
theorem hasAboveReturns_compWitness (ha : 0 < a) (hb : 0 < b) (hpos : ∀ x ∈ α, 0 < x)
    (hsum : α.sum = N) : HasAboveReturns α (compWitness a b N α) := by
  refine ⟨isAboveDiagonal_compWitness ha hsum, hpos, hsum, fun k hk => ?_⟩
  have hak : a * k ≤ a * N := Nat.mul_le_mul le_rfl hk
  rw [ht_compWitness' hsum hak]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have heq : compReach a α (a * k) = k := Nat.eq_of_mul_eq_mul_left hb h
    exact heq ▸ (compReach_mem (a := a) hsum hak).1
  · rw [compReach_mul ha h hsum hk]

/-! ### The admissibility conjunct -/

/-- **The first conjunct of `HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc`: `c_α`
is an admissible colouring at a separating admissible level.** By `HJO.Mellit.IsAdmissibleColouring`
this asks for an above-diagonal `(aN, bN)`-path coloured `c_α`, and
`HJO.Mellit.colouring_eq_compColouring_iff` says that at such a level the paths coloured `c_α` are
exactly those of return composition `α`; the witness is therefore `HJO.Mellit.compWitness`.

Nothing about the coefficient field, the scalars `q`, `u` or the realisation enters: this is a
statement about lattice paths in the rectangle, and `HJO.Mellit.Rem41` does not state it at all. -/
theorem isAdmissibleColouring_compColouring {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (hpos : ∀ x ∈ α, 0 < x) (hsum : α.sum = N) :
    IsAdmissibleColouring a b N η (compColouring a b α) :=
  ⟨compWitness a b N α, isAboveDiagonal_compWitness ha hsum,
    (colouring_eq_compColouring_iff hηa hηs hab ha hb hpos hsum
      (isAboveDiagonal_compWitness ha hsum)).2 (hasAboveReturns_compWitness ha hb hpos hsum)⟩

/-- **The left-hand sum of `HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc` is never
vacuous.** The index set contains the witness path, so the identity compares a nonempty sum with the
invariant. No level and no scalars are read: the statement is about the index set alone. -/
theorem aboveReturnPaths_nonempty (ha : 0 < a) (hb : 0 < b) (hpos : ∀ x ∈ α, 0 < x)
    (hsum : α.sum = N) : (aboveReturnPaths a b N α).Nonempty :=
  ⟨compWitness a b N α, by
    simp only [aboveReturnPaths, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨isAboveDiagonal_compWitness ha hsum, hasAboveReturns_compWitness ha hb hpos hsum⟩⟩

/-! ### The identity, from `HJO.Mellit.sweepComputes` -/

section Identity

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The second conjunct of `HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc` from
`HJO.Mellit.sweepComputes`**, in the statement's own shape: no `HJO.Mellit.SweepSystem`, and so none
of the pinning hypotheses `hchi` and `hD` that `HJO.Mellit.rem41_of_sweepComputes` needs in order to
say the same thing about an abstract system. The argument:
`HJO.Mellit.dsc_compColouring_eq_sum_partialSweepWord` expands `D_{η,c_α}` as `∑_{P̂} W_η(P̂)(1)`
over this very index set, `HJO.Mellit.sweepWord_vac_eq` factors
`W(P̂)(1) = u^{N-ℓ} d_-^ℓ(W_η(P̂)(1))`, and `SweepComputes` evaluates each `ι(W(P̂)(1))` as the
summand. The finitely many summands are gathered under one `ι` by its linearity.

The exponent `N - ℓ` of `u` is a natural number and no inverse of `u` is taken; the negative
exponent of `q` on the left is carried through untouched. -/
theorem sum_sweepChar_eq_smul_dsc_of_sweepComputes (q u : L) (hab : Nat.Coprime a b) (ha : 0 < a)
    (hb : 0 < b) {ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L} (hι : Sym.IsRealisation ι)
    {η : ℚ} (hηa : IsAdmissibleLevel η) (hηs : SeparatesDiagonal a b N η)
    (hpos : ∀ x ∈ α, 0 < x) (hsum : α.sum = N) (h : SweepComputes q u a b) :
    ∑ y ∈ aboveReturnPaths a b N α,
        (u ^ Paths.aboveArea y *
            q ^ ((Paths.aboveHookCount y : ℤ) - (aboveMaxTdinv y : ℤ))) • Paths.sweepChar q y
      = u ^ (N - α.length) •
          ι (MvPolynomial.constantCoeff
            (lowerRun q α.length (dsc q u a b N η (compColouring a b α)))) := by
  rw [dsc_compColouring_eq_sum_partialSweepWord q u hηa hηs hab ha hb hpos hsum]
  simp only [map_sum]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [aboveReturnPaths, Finset.mem_filter] at hy
  rw [← h ι hι N y hy.2.1, sweepWord_vac_eq q u hηa hηs hab ha hb hy.2.2,
    MvPolynomial.constantCoeff_smul, map_smul]

/-- **`HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc` under the three conditions on
`q` that `HJO.Mellit.sweepComputes` itself carries**, which is the sharpest form of the statement
available: `q ≠ 0` from collecting the scalars of `HJO.Mellit.sweepOperator`, `q ≠ 1` from
`HJO.Mellit.map_constantCoeff_markedWordOp'` at a nonempty marking, and
`∀ r, IsUnit (q ^ (r + 1) - 1)` from `HJO.Dyck.auxZeroMap_eq_pathCharSeries_of_isSigmaCharacter`.
Nothing is asked of `u`.

The first conjunct does not read them — `HJO.Mellit.isAdmissibleColouring_compColouring` holds at
every `q` — so the conditions are spent by the identity alone. -/
theorem isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc_of_q (q u : L) (hq0 : q ≠ 0)
    (hq1 : q ≠ 1) (hqu : ∀ r : ℕ, IsUnit (q ^ (r + 1) - 1)) (hab : Nat.Coprime a b) (ha : 0 < a)
    (hb : 0 < b) {ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L} (hι : Sym.IsRealisation ι)
    {η : ℚ} (hηa : IsAdmissibleLevel η) (hηs : SeparatesDiagonal a b N η)
    (hpos : ∀ x ∈ α, 0 < x) (hsum : α.sum = N) :
    IsAdmissibleColouring a b N η (compColouring a b α) ∧
      ∑ y ∈ aboveReturnPaths a b N α,
          (u ^ Paths.aboveArea y *
              q ^ ((Paths.aboveHookCount y : ℤ) - (aboveMaxTdinv y : ℤ))) • Paths.sweepChar q y
        = u ^ (N - α.length) •
            ι (MvPolynomial.constantCoeff
              (lowerRun q α.length (dsc q u a b N η (compColouring a b α)))) :=
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  ⟨isAdmissibleColouring_compColouring hηa hηs hab ha hb hpos hsum,
    sum_sweepChar_eq_smul_dsc_of_sweepComputes q u hab ha hb hι hηa hηs hpos hsum
      (sweepComputes q u hq0 hq1 hqu)⟩

/-- **Mellit's Remark 4.1, the composition sum as an invariant.** At a level
`η` separating the diagonal of the `aN × bN` rectangle, the colouring `c_α` of a composition `α` of
`N` is an admissible colouring, and for every realisation `ι`

`∑_{P̂} u^{ârea(P̂)} q^{ĥ(P̂) - max t̂dinv(P̂)} χ(P̂) = ι(u^{N-ℓ} d_-^ℓ D_{η,c_α})`,

the sum running over the above-diagonal `(aN, bN)`-paths of return composition `α`.

The slope is any coprime pair of positive integers, the natural hypothesis here; the standing
assumption `1 < a < b` is spent nowhere. The `d_-^ℓ` is the composite of `d_-` at the
graded indices `1, …, ℓ`, which is `HJO.Mellit.lowerRun q ℓ`; `V_0 = Λ` is read by
`MvPolynomial.constantCoeff`, and `ι` carries that reading into the power series ring where the
path sum lives.

**The binder on the scalars is the ambient one.** The statement carries no condition
on `q` because the ambient field is `𝕜 := ℚ(q,u)`, the field of rational functions in two
indeterminates; `AlgebraicIndependent ℤ ![q, u]` is how that standing hypothesis is
rendered here, and it is the binder `HJO.Mellit.MellitInput` and
`HJO.Mellit.shuffle_of_three` already carry. It is what discharges the three conditions of
`HJO.Mellit.sweepComputes` — see `HJO.Mellit.sweepComputes_of_algebraicIndependent` — and it costs
nothing where the theorem is used: `HJO.shuffleAbove` reaches it through
`HJO.Mellit.shuffle_of_lhs_and_induction`, which quantifies over exactly it. For the statement at an
arbitrary `q` satisfying only what `HJO.Mellit.sweepComputes` needs, see
`HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc_of_q`; for the first conjunct with
no condition on the scalars whatever, `HJO.Mellit.isAdmissibleColouring_compColouring`. -/
@[hjo "lem_mellit_rem41"]
theorem isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc (q u : L)
    (hind : AlgebraicIndependent ℤ ![q, u]) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L} (hι : Sym.IsRealisation ι)
    {η : ℚ} (hηa : IsAdmissibleLevel η) (hηs : SeparatesDiagonal a b N η)
    (hpos : ∀ x ∈ α, 0 < x) (hsum : α.sum = N) :
    IsAdmissibleColouring a b N η (compColouring a b α) ∧
      ∑ y ∈ aboveReturnPaths a b N α,
          (u ^ Paths.aboveArea y *
              q ^ ((Paths.aboveHookCount y : ℤ) - (aboveMaxTdinv y : ℤ))) • Paths.sweepChar q y
        = u ^ (N - α.length) •
            ι (MvPolynomial.constantCoeff
              (lowerRun q α.length (dsc q u a b N η (compColouring a b α)))) :=
  ⟨isAdmissibleColouring_compColouring hηa hηs hab ha hb hpos hsum,
    sum_sweepChar_eq_smul_dsc_of_sweepComputes q u hab ha hb hι hηa hηs hpos hsum
      (sweepComputes_of_algebraicIndependent q u hind a b)⟩

end Identity

end HJO.Mellit
