/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.BwordBasisAll
public import HJO.CarlssonMellit.SweepCM
public import HJO.Shuffle.SweepBasis
public meta import HJO.Attr

/-! # Carlsson and Mellit's monomial basis of `V_*`

`HJO.Sweep.exists_basis_vstar_prod_bop`, the SPANNING PRINCIPLE of Carlsson and Mellit's Lemma 5.6:
the elements

`y_1^{a_1} ⋯ y_k^{a_k} B_{a_{k+1}+1}(B_{a_{k+2}+1}(⋯ B_{a_{k+m}+1}(1)⋯)) ∈ V_k`,

indexed by `k, m ≥ 0` and exponents `a_1, …, a_{k+m} ≥ 0` with `a_{k+1} ≥ ⋯ ≥ a_{k+m}`, form a
`𝕜`-basis of `V_* = ⨁_{k ≥ 0} V_k`. It is what licenses the reductions "evaluate on `y_k^a`" that
the starred relations are proved by.

## Main results

* `HJO.Sweep.exists_basis_vstar_prod_bop`.

## Implementation notes

**Every input is proved elsewhere; this file is the assembly.** `HJO.Sym.exists_basis_prod_bop_one`
is the basis of `Λ` by the words of the Hall--Littlewood operators, `HJO.Sym.shiftPartitionEquiv`
(`HJO.Sym.sortedPartitionEquiv`) reindexes it by the weakly decreasing tuples the display names,
`HJO.Sweep.pieceBasis` (`HJO.Sweep.pieceSubBasis`) turns a basis of `Λ` into the basis
`y_1^{a_1} ⋯ y_k^{a_k}f_i` of `V_k`, and `DFinsupp.basis` glues bases of the summands of a direct
sum — `V_*` being the external direct sum `HJO.Sweep.Vstar` of the `V_k`, not the union of the
nested pieces.

**The index.** The single tuple `a_1, …, a_{k+m}` with the constraint on its tail is
carried here by a pair: `a : Fin k →₀ ℕ`, the unconstrained `y`-exponents, and
`l : {l : List ℕ // l.SortedGE}`, the weakly decreasing tail `a_{k+1} ≥ ⋯ ≥ a_{k+m}` whose length is
the `m`. The parts of the word are `l` raised by one, which is the display's
`B_{a_{k+i}+1}`, and the operators are applied innermost-first in nonincreasing order — they do not
commute, so that order is part of the statement.

**How the basis vector is pinned.** A member of `V_*` is a finitely supported family, so saying what
the displayed element IS has two halves: the basis vector is the image under
`HJO.Sweep.ofPiece` of an element of the `k`-th summand — so it is concentrated there, as the image
of an element of `V_k` in the direct sum must be — and that element has the displayed value in the
total space `HJO.Sweep.Total`, where the product of a `y`-monomial with a symmetric function is
written. Both halves are recorded, the second through the coercion `pieceSub L k → Total L`, which
is how every other statement about an element of `V_k` in this library reads its value off.

**The base.** `q` is an arbitrary element of the base ring rather than Carlsson and Mellit's
transcendental: the basis of `Λ` behind the statement holds for every `q`, since the triangularity
proving it has diagonal `(-1)^d`. The base is a commutative `ℚ`-algebra, `ℚ` entering only because
the elementary symmetric functions inside `HJO.Sym.Bop` are defined by Newton's identities; Carlsson
and Mellit's `𝕜 = ℚ(q, u)` is a case of it.

## References

Transcribing E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, the second half of its
Lemma 5.6, whose quotation of Hall--Littlewood theory is replaced here by triangularity against the
elementary monomials.
-/

@[expose] public section

namespace HJO.Sweep

variable {L : Type*} [CommRing L] [Algebra ℚ L]

/-- **Carlsson and Mellit's monomial basis of `V_*`.** The elements

`y_1^{a_1} ⋯ y_k^{a_k} B_{a_{k+1}+1}(B_{a_{k+2}+1}(⋯ B_{a_{k+m}+1}(1)⋯)) ∈ V_k`,

indexed by `k, m ≥ 0` and exponents `a_1, …, a_{k+m} ≥ 0` with `a_{k+1} ≥ ⋯ ≥ a_{k+m}`, form a
`𝕜`-basis of `V_*`. The unconstrained head `(a_1, …, a_k)` is `a : Fin k →₀ ℕ` and the weakly
decreasing tail is `l`, of length `m`; the word of Hall--Littlewood operators along `l` raised by
one is the product of the `HJO.Sym.Bop q` in `Module.End 𝕜 Λ` applied to `1`.

The basis vector at `(k, a, l)` lies in the `k`-th summand of `V_*` — it is `HJO.Sweep.ofPiece` of
an element of `V_k` — and that element of `V_k` is the displayed product, read in the total
space. -/
@[hjo "lem_cm_algbasis_module"]
theorem exists_basis_vstar_prod_bop (q : L) :
    ∃ B : Module.Basis (Σ k : ℕ, (Fin k →₀ ℕ) × {l : List ℕ // l.SortedGE}) L (Vstar L),
      ∀ (k : ℕ) (a : Fin k →₀ ℕ) (l : {l : List ℕ // l.SortedGE}),
        ∃ F : pieceSub L k, B ⟨k, (a, l)⟩ = ofPiece L k F ∧
          (F : Total L) = (∏ j : Fin k, (auxVar ((j : ℕ) + 1) : Total L) ^ a j) *
            algebraMap (Sym.Lambda L) (Total L)
              (((l.1.map (· + 1)).map fun r : ℕ => Sym.Bop q (r : ℤ)).prod 1) := by
  classical
  obtain ⟨bLam, hbLam⟩ := Sym.exists_basis_prod_bop_one (K := L) q
  set b : Module.Basis {l : List ℕ // l.SortedGE} L (Sym.Lambda L) :=
    bLam.reindex Sym.sortedPartitionEquiv.symm with hb
  have hbval : ∀ l : {l : List ℕ // l.SortedGE},
      b l = ((l.1.map (· + 1)).map fun r : ℕ => Sym.Bop q (r : ℤ)).prod 1 := by
    intro l
    rw [hb, Module.Basis.reindex_apply, Equiv.symm_symm, hbLam,
      Sym.sort_parts_sortedPartitionEquiv]
  refine ⟨DFinsupp.basis fun k => pieceSubBasis k b, fun k a l => ?_⟩
  refine ⟨pieceSubBasis k b (a, l), ?_, ?_⟩
  · have hsingle : (DFinsupp.basis fun k => pieceSubBasis k b) ⟨k, (a, l)⟩
        = DFinsupp.single k (pieceSubBasis k b (a, l)) := by simp [DFinsupp.basis]
    rw [hsingle]
    rfl
  · rw [coe_pieceSubBasis_eq_prod, hbval]

end HJO.Sweep
