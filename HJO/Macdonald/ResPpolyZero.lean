/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.PpolyCut
public import HJO.Macdonald.PpolyCutZero
public meta import HJO.Attr

/-! # Restriction to a short alphabet kills a long Macdonald symmetric function

`HJO.Mac.restrictAlphabet_macPfun_eq_zero`: for a partition `μ` with `μ_{n+1} ≥ 1`,
`res_n(P_μ) = 0`. This is the complement of `HJO.Mac.restrictAlphabet_macPfun_partDiagram_of_pos`,
which covers `μ_{n+1} = 0`; between them `res_n(P_μ)` is known for every `n` and every `μ`.

## The route

Let `m` be the largest index with `μ_{m+1} ≥ 1` — in Lean, with
`μ.rowLen m ≠ 0`, which exists because `rowLen` vanishes from `|μ|` on
(`HJO.Mac.rowLen_eq_zero_of_card_le`) and is found by `Nat.findGreatest`. The hypothesis puts
`n ≤ m`, and `μ.rowLen (m+1) = 0` by maximality.

At the alphabet `Fin (m+1)` the diagram `μ` is untruncated, so
`HJO.Mac.restrictAlphabet_macPfun_partDiagram_of_pos` gives `res_{m+1}(P_μ) = P_μ[X_{m+1}]`; and `μ`
has *full length* there, every one of the `m+1` rows being nonempty, so
`HJO.Mac.killCompl_macPpoly_eq_zero` kills it under `cut_m`. Since `cut_m ∘ res_{m+1} = res_m`
(`HJO.Sym.killCompl_restrictAlphabet`), `res_m(P_μ) = 0`. Below `m` there is nothing left to do:
`res_j = cut_j ∘ res_{j+1}` and `cut_j` is linear, so a downward induction from `m` to `n` carries
the vanishing.

Full length is where this file spends its one new lemma, `HJO.Mac.card_le_of_one_le_partExp` — the
converse of `HJO.Mac.one_le_partExp_of_card_le` in `HJO/Macdonald/PpolyCutZero.lean`. The
hypothesis of `HJO.Mac.killCompl_macPpoly_eq_zero` is stated as a count of parts, while what is
available here is that every row length up to `m` is nonzero, and the two are the same condition.

## Generality, and a hypothesis that is dropped

The `n ≥ 1` is absent. The downward induction runs to `j = 0` without knowing anything
about the alphabet, and the statement at `n = 0` is true and not vacuous: `μ.rowLen 0 ≠ 0` says `μ`
is nonempty, and `res_0(P_μ)` is a symmetric polynomial in no variables that is homogeneous of
degree `|μ| ≥ 1`, hence `0`.

The field and the genericity hypothesis are exactly those needed to name `P_μ` (`HJO.Sym.macPfun`);
no further arithmetic in `q` or `u` is spent.

## Main results

* `HJO.Mac.card_le_of_one_le_partExp`: an index whose exponent vector is everywhere positive has
  full length.
* `HJO.Mac.restrictAlphabet_macPfun_eq_zero_of_rowLen_succ_eq_zero`: the vanishing at the largest
  alphabet where it holds, `n = m`, which is the one step of the proof that is not
  bookkeeping.
* `HJO.Mac.restrictAlphabet_macPfun_eq_zero`.

## References

This file proves `HJO.Mac.restrictAlphabet_macPfun_eq_zero`, on the definitions `HJO.Sym.rowLenSeq`,
`HJO.Sym.restrictAlphabet` and `HJO.Sym.macPfun` and the lemmas
`HJO.Sym.killCompl_restrictAlphabet`, `HJO.Mac.killCompl_macPpoly_eq_zero` and
`HJO.Mac.restrictAlphabet_macPfun_partDiagram_of_pos`. The consumer is
`HJO.Ascent.elemSymm_one_mul_macPfun_mem_span_covers_or_short`.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Mac

/-- **An index whose exponent vector is everywhere positive has full length**, the converse of
`HJO.Mac.one_le_partExp_of_card_le`: the multiset `partSym τ μ` then meets every letter, so its
distinct elements are all of `τ` and the partition has `#τ` parts. Together the two say that "full
length" and "every entry positive" are the same condition on an index, which is what lets a
consumer holding row lengths discharge the hypothesis of `HJO.Mac.killCompl_macPpoly_eq_zero`. -/
theorem card_le_of_one_le_partExp {τ : Type*} [LinearOrder τ] [Fintype τ] {D : ℕ}
    (μ : PartIdx τ D) (h : ∀ i : τ, 1 ≤ partExp τ μ i) : Fintype.card τ ≤ μ.1.parts.card := by
  classical
  have hpc : μ.1.parts.card = (partSym τ μ).1.toFinset.card := by
    rw [← ofSym_partSym μ, Nat.Partition.parts_ofSym, Multiset.card_map, Multiset.card_toFinset]
  rw [hpc, ← Finset.card_univ]
  refine Finset.card_le_card fun i _ => Multiset.mem_toFinset.mpr ?_
  have hi := h i
  rw [partExp, Multiset.toFinsupp_apply] at hi
  exact Multiset.one_le_count_iff_mem.mp hi

variable {K : Type*} [Field K] [Algebra ℚ K] {q : Kˣ} {u : K}

/-- **Restriction to the alphabet `Fin m` kills `P_μ` when row `m` of `μ` is the last nonempty
one.** This is the step at `l - 1`: at the alphabet `Fin (m+1)` the diagram is
untruncated, so `res_{m+1}(P_μ) = P_μ[X_{m+1}]`
(`HJO.Mac.restrictAlphabet_macPfun_partDiagram_of_pos`), and it has full length there because rows
`0, …, m` are all nonempty, so `HJO.Mac.killCompl_macPpoly_eq_zero` kills it under `cut_m`.
`HJO.Sym.killCompl_restrictAlphabet` identifies `cut_m ∘ res_{m+1}` with `res_m`. -/
theorem restrictAlphabet_macPfun_eq_zero_of_rowLen_succ_eq_zero
    (hqu : AlgebraicIndependent ℤ ![(q : K), u]) {m : ℕ} {μ : YoungDiagram}
    (hm : μ.rowLen m ≠ 0) (hm1 : μ.rowLen (m + 1) = 0) :
    HJO.Sym.restrictAlphabet (Fin m) K (HJO.Sym.macPfun hqu μ) = 0 := by
  obtain ⟨ν, hν⟩ :=
    exists_partDiagram_eq (σ := Fin (m + 1)) (by rw [Fintype.card_fin]; exact hm1)
  have h0 := restrictAlphabet_macPfun_partDiagram_of_pos hqu (Nat.succ_le_succ (Nat.zero_le m)) ν
  rw [hν] at h0
  -- `μ` has a nonempty row at every letter of `Fin (m+1)`, so the index has full length
  have hfull : Fintype.card (Fin (m + 1)) ≤ ν.1.parts.card := by
    refine card_le_of_one_le_partExp ν fun i => ?_
    obtain ⟨k, rfl⟩ := (letterEquiv (Fin (m + 1))).surjective i
    have hk : (k : ℕ) ≤ m :=
      Nat.lt_succ_iff.mp (lt_of_lt_of_eq k.isLt (Fintype.card_fin (m + 1)))
    have h1 : rowLenSeqOf (Fin (m + 1)) (partExp (Fin (m + 1)) ν) (k : ℕ)
        = partExp (Fin (m + 1)) ν (letterEquiv (Fin (m + 1)) k) := rowLenSeqOf_of_lt k.isLt
    have h2 : partExp (Fin (m + 1)) ν (letterEquiv (Fin (m + 1)) k) = μ.rowLen (k : ℕ) := by
      rw [← h1, ← rowLen_partDiagram, hν]
    rw [h2]
    exact Nat.one_le_iff_ne_zero.mpr fun hz =>
      hm (Nat.le_zero.mp (hz ▸ μ.rowLen_anti _ _ hk))
  have hzero := killCompl_macPpoly_eq_zero hqu hfull (Fin.castSucc_injective m)
    (t := Fin.last m) (by rintro ⟨i, hi⟩; exact absurd hi (Fin.castSucc_lt_last i).ne)
  rw [← HJO.Sym.killCompl_restrictAlphabet (Fin.castSucc_injective m) (HJO.Sym.macPfun hqu μ),
    h0, hzero]

/-- **Restriction to a short alphabet kills a long Macdonald symmetric
function.** If `μ` has a nonempty row at index `n` — the `μ_{n+1} ≥ 1` — then
`res_n(P_μ) = 0`.

Take `m` largest with row `m` of `μ` nonempty; then `n ≤ m`,
`restrictAlphabet_macPfun_eq_zero_of_rowLen_succ_eq_zero` gives the vanishing at `m`, and
`HJO.Sym.killCompl_restrictAlphabet` carries it down to `n`, `cut_j` being linear. The `n ≥ 1` is
not needed. -/
@[hjo "lem_pie_res_ppoly_zero"]
theorem restrictAlphabet_macPfun_eq_zero (hqu : AlgebraicIndependent ℤ ![(q : K), u]) {n : ℕ}
    {μ : YoungDiagram} (hμ : μ.rowLen n ≠ 0) :
    HJO.Sym.restrictAlphabet (Fin n) K (HJO.Sym.macPfun hqu μ) = 0 := by
  classical
  have hnc : n ≤ μ.card := by
    by_contra hc
    exact hμ (rowLen_eq_zero_of_card_le (by omega))
  obtain ⟨m, hm, hnm, hm1⟩ : ∃ m : ℕ, μ.rowLen m ≠ 0 ∧ n ≤ m ∧ μ.rowLen (m + 1) = 0 := by
    refine ⟨Nat.findGreatest (fun k => μ.rowLen k ≠ 0) μ.card,
      Nat.findGreatest_spec (P := fun k => μ.rowLen k ≠ 0) hnc hμ,
      Nat.le_findGreatest (P := fun k => μ.rowLen k ≠ 0) hnc hμ, ?_⟩
    rcases le_or_gt (Nat.findGreatest (fun k => μ.rowLen k ≠ 0) μ.card + 1) μ.card with hle | hgt
    · exact not_not.mp (Nat.findGreatest_is_greatest (P := fun k => μ.rowLen k ≠ 0)
        (Nat.lt_succ_self _) hle)
    · exact rowLen_eq_zero_of_card_le (by omega)
  -- descend from `m` to `n`, one variable at a time
  have key : ∀ k j : ℕ, j + k = m →
      HJO.Sym.restrictAlphabet (Fin j) K (HJO.Sym.macPfun hqu μ) = 0 := by
    intro k
    induction k with
    | zero =>
        intro j hj
        rw [Nat.add_zero] at hj
        subst hj
        exact restrictAlphabet_macPfun_eq_zero_of_rowLen_succ_eq_zero hqu hm hm1
    | succ k ih =>
        intro j hj
        have h1 : HJO.Sym.restrictAlphabet (Fin (j + 1)) K (HJO.Sym.macPfun hqu μ) = 0 :=
          ih (j + 1) (by omega)
        rw [← HJO.Sym.killCompl_restrictAlphabet (Fin.castSucc_injective j)
          (HJO.Sym.macPfun hqu μ), h1, map_zero]
  exact key (m - n) n (by omega)

end HJO.Mac
