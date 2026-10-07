/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Ascent.Ascend
public import HJO.Collinear.Commutation
public import HJO.Collinear.Diagonal
public import HJO.Collinear.IndexShiftStanding
public import HJO.Macdonald.EigenbasisClosed

/-! # The collinear input costs one Prop at one field

The collinear half of this library would otherwise ask for a Macdonald conjugator **at every field
of characteristic zero carrying an algebraically independent pair of parameters**: that is the shape
of the `hconj` binder of `HJO.Debt.conjecture_of_debt`, and it is what
`HJO.CollinearNarrowed.collinearCommutation_of_structures` consumes.

That shape is much stronger than the mathematics needs, and this file removes the excess. The
obligation here is `HJO.Sym.HasPieriEigenfamily (paramQ K) (paramU K)` -- one `Prop`, at the
standing coefficient field `𝕜 = ℚ(q, u)` alone.

## Why the general field was never needed

`HJO.Ascent.commute_qop_ascend` already proves that a commutation of slope operators ASCENDS: if
`Q_{m,n}` and `Q_{m',n'}` commute at the standing instance, they commute at any field of
characteristic zero carrying an algebraically independent pair. It was stated with the `𝕜`-side
commutation as a hypothesis precisely because that side was the Macdonald material still owed, and
its docstring says that once that material exists "this theorem is the whole of the passage to the
model's coefficient field -- there is nothing else to supply".

So the collinear chain only ever needed its inputs at `𝕜`, and every one of them is available
there already:

* the conjugator -- `HJO.Standing.exists_isMacdonaldConjugator_of_hasPieriEigenfamily_param'`, whose
  only remaining input is the Pieri eigenfamily, the unnormalised eigenbasis having been closed
  outright in `HJO/Macdonald/EigenbasisClosed.lean`;
* the index shift -- `HJO.Bglx.exists_isIndexShift_param`, with no hypothesis at all;
* the diagonal base case -- `HJO.Sym.qop_diag_commute`, from the conjugator and three parameter
  conditions;
* those three conditions -- `(1-q)(1-u) ≠ 0`, `qu ≠ 0` and `qu ≠ 1` -- from
  `HJO.Ascent.algebraicIndependent_param`, so none of them appears below.

This matters beyond bookkeeping. `hconj` at a general field is not merely unnecessary, it cannot be
proved by the route this library uses: that route goes through
`HJO.Sym.exists_isMacdonaldConjugator_of_hasPieriEigenfamily`, which needs a ring involution `ι` of
the coefficient field with `ι q = q⁻¹` and `ι u = u⁻¹`, and no such involution exists at a
general field even at an algebraically independent pair -- over `ℝ` the only ring endomorphism is
the identity, while `ℝ` has algebraically independent pairs in abundance. The parameter
inversions exist at `𝕜` because `q` and `u` are indeterminates there, which is exactly what
`HJO/Ascent/` was built to exploit and exactly why it cannot be dispensed with here.

## What this leaves

`HJO.Sym.HasPieriEigenfamily (paramQ K) (paramU K)` is
`HJO.Standing.elemSymm_one_mul_macHtilde_mem_span_param`. It reduces in turn to
`HJO.Sym.HasPfunPieriSupport` together with the `D_0` relation already available, and the Macdonald
duality block below it is unavoidable -- established by counterexample rather than estimated: at
`ν = (3,2,2,1)` the partition `λ = (3,3,1,1,1)` survives dominance triangularity, the lex leading
exponent, `λ₁ ≤ ν₁` and the column-removal induction all at once, while the conjugate partitions
exclude it immediately.
-/

@[expose] public section

namespace HJO.CollinearNarrowed

open HJO.Sym HJO.Ascent HJO.Standing HJO.Bglx

variable (K : Type*) [Field K] [Algebra ℚ K] [Algebra ParamRing K] [IsFractionRing ParamRing K]

/-- **The collinear operators commute at the standing field, from the Pieri eigenfamily alone.**

The Euclidean descent of `HJO.Sym.collinear_commute_of_diag` with all four of its inputs
supplied at `𝕜`: the conjugator from `hpieri`, the index shift from
`HJO.Bglx.exists_isIndexShift_param`, the diagonal base case from `HJO.Sym.qop_diag_commute`, and
the three parameter conditions from the algebraic independence of the two indeterminates. -/
theorem commute_qop_param (hpieri : HasPieriEigenfamily (paramQ K) (paramU K))
    {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) {k l : ℕ} (hk : 0 < k)
    (hl : 0 < l) :
    Commute (Qop (paramQ K) (paramU K) (k * a) (k * b))
      (Qop (paramQ K) (paramU K) (l * a) (l * b)) := by
  have hqu := algebraicIndependent_param K
  have hM := one_sub_mul_one_sub_ne_zero_of_algebraicIndependent hqu
  have hv0 := mul_ne_zero_of_algebraicIndependent hqu
  have hv1 : paramQ K * paramU K ≠ 1 := by
    simpa using pow_succ_ne_one_of_algebraicIndependent hqu 0
  have hconj := exists_isMacdonaldConjugator_of_hasPieriEigenfamily_param' K hpieri
  exact collinear_commute_of_diag hM hconj (exists_isIndexShift_param K)
    (fun k l hk hl => qop_diag_commute hM hv0 hv1 hconj hk hl) a b hab ha hb k l hk hl

/-- **The narrowed collinear input at every coefficient field, from one `Prop` at the standing
field.** `HJO.CollinearNarrowed.CollinearCommute L` for an arbitrary field `L` of characteristic
zero, given only the Pieri eigenfamily at `𝕜`.

The descent runs at `𝕜`, where the parameter inversions the Macdonald chain needs exist, and
`HJO.Ascent.commute_qop_ascend` carries each resulting commutation to `L` along the embedding of
`𝕜` determined by the algebraically independent pair the clause is stated at. -/
theorem collinearCommute_of_pieri_param (hpieri : HasPieriEigenfamily (paramQ K) (paramU K))
    (L : Type*) [Field L] [Algebra ℚ L] : CollinearCommute L := by
  intro a b hab ha hb q u hqu k l hk hl
  have hstd := commute_qop_param K hpieri hab (by omega) (by omega) hk hl
  have hasc := commute_qop_ascend K hqu hstd
  rwa [Nat.mul_comm k a, Nat.mul_comm k b, Nat.mul_comm l a, Nat.mul_comm l b] at hasc

/-- **The collinear input, from one `Prop` at one field.**
`HJO.External.CollinearCommutation L` -- the quoted input in the form every consumer of this
library takes it -- follows from `HJO.Sym.HasPieriEigenfamily (paramQ K) (paramU K)` alone.

This supersedes `HJO.CollinearNarrowed.collinearCommutation_of_structures` as the statement of what
the collinear side costs. That theorem asked for a conjugator and an index shift at every field with
an algebraically independent pair; the index shift is now a theorem, and the conjugator is needed
only at `𝕜`, where it reduces to this one `Prop`. -/
theorem collinearCommutation_of_pieri_param (hpieri : HasPieriEigenfamily (paramQ K) (paramU K))
    (L : Type*) [Field L] [Algebra ℚ L] : HJO.External.CollinearCommutation L :=
  collinearCommutation (collinearCommute_of_pieri_param K hpieri L)

end HJO.CollinearNarrowed
