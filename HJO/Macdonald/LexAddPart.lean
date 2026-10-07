/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.PartitionInsert
public import HJO.Macdonald.PartitionLex
public meta import HJO.Attr

/-! # Adding a part preserves the lexicographic order

`HJO.Sym.partitionLex_insertPart`: if `μ > λ'` lexicographically and `c ≥ λ'_1` with `c ≥ 1`, then
`c ∪ μ > c ∪ λ'`.

## The two cases of the proof

Since `c ≥ λ'_1`, the insertion into `λ'` stops at the front, so
`c ∪ λ' = (c, λ'_1, λ'_2, …)` — that is `HJO.Sym.rowLen_insertPart_zero` and
`HJO.Sym.rowLen_insertPart_succ`. For `μ` the argument splits:

* `μ_1 > c`. Then the first row of `c ∪ μ` is at least `μ_1 > c`, which is the first row of
  `c ∪ λ'`, so row `0` already witnesses the comparison. The bound
  `μ_1 ≤ (c ∪ μ)_1` needs no case analysis on where `c` lands: `μ_1` is one of the parts of `c ∪ μ`,
  and row `0` is the longest.
* `μ_1 ≤ c`. Then `c ∪ μ = (c, μ_1, μ_2, …)` as well, the two agree in row `0`, and the witness `i`
  of `μ > λ'` becomes the witness `i + 1`.

## What is dropped, and why

As usually stated, the lemma asks that `λ'` and `μ` be partitions of one and the same `n`, so that
`HJO.Sym.partitionLex` — stated for partitions of a fixed degree — applies to `c ∪ μ` and `c ∪ λ'`.
`HJO.Sym.partitionLex` carries no such condition (its own docstring records that equal size matters
to the consumers and not to the order), and nothing in the argument above reads it. So the
hypothesis is dropped, which only generalises the statement; `HJO.Sym.card_insertPart` is the fact a
consumer needs if it wants it back, `|c ∪ ν| = |ν| + c`.

`c ≥ 1` is genuinely needed and not bookkeeping: `YoungDiagram.ofRowLens` silently drops a zero row,
so at `c = 0` the insertion is the identity and the conclusion would be the hypothesis with the
rows unshifted — every statement of `HJO.Macdonald.PartitionInsert` carries it for the same
reason.

## References

The lemma `HJO.Sym.partitionLex_insertPart`, used for the Haglund--Morse--Zabrocki relations, and
the definitions `HJO.Sym.insertPart` and `HJO.Sym.partitionLex`.
-/

@[expose] public section

namespace HJO.Sym

/-- The longest row of a nonempty diagram occurs in its list of row lengths. -/
theorem rowLen_zero_mem_rowLens {nu : YoungDiagram} (h : 0 < nu.rowLen 0) :
    nu.rowLen 0 ∈ nu.rowLens := by
  have h0 := nu.rowLen_eq_getD 0
  match hl : nu.rowLens with
  | [] =>
    rw [hl] at h0
    simp only [List.getD_nil] at h0
    omega
  | b :: l =>
    have hb : nu.rowLen 0 = b := by rw [hl] at h0; simpa using h0
    rw [hb]
    simp

/-- **Every part of `ν` is at most the first part of `c ∪ ν`.** The parts of `c ∪ ν` are those of
`ν` together with `c`, and row `0` of a diagram is its longest. No relation between `c` and the rows
of `ν` is assumed, which is what the case `μ_1 > c` of `HJO.Sym.partitionLex_insertPart` needs. -/
theorem le_rowLen_insertPart_zero_of_mem {c : ℕ} (hc : 0 < c) (nu : YoungDiagram) {x : ℕ}
    (hx : x ∈ nu.rowLens) : x ≤ (insertPart c nu).rowLen 0 := by
  have hmem : x ∈ (insertPart c nu).rowLens := by
    have h := rowLens_insertPart_toMultiset hc nu
    have hx' : x ∈ (c ::ₘ (nu.rowLens : Multiset ℕ)) := Multiset.mem_cons_of_mem hx
    rw [← h] at hx'
    exact hx'
  obtain ⟨i, hi, hci⟩ := List.mem_iff_getElem.1 hmem
  have hce : (insertPart c nu).rowLen i = x := (YoungDiagram.get_rowLens (h := hi)).symm.trans hci
  exact hce.symm.trans_le ((insertPart c nu).rowLen_anti 0 i (Nat.zero_le i))

/-- **Adding a part preserves the lexicographic order.** If `μ > λ'` and
`c ≥ λ'_1` with `c ≥ 1`, then `c ∪ μ > c ∪ λ'`.

Two cases. If `μ_1 > c` the two first rows already differ, `c ∪ λ'` having
first row `c` while `c ∪ μ` has first row at least `μ_1`. If `μ_1 ≤ c` both insertions stop at the
front, so the two agree in row `0` and carry `μ_i`, `λ'_i` in row `i + 1`; the witness of `μ > λ'`
shifts by one. -/
@[hjo "lem_cm_lex_add_part"]
theorem partitionLex_insertPart {lam mu : YoungDiagram} (h : partitionLex lam mu) {c : ℕ}
    (hc : 0 < c) (hlam : lam.rowLen 0 ≤ c) :
    partitionLex (insertPart c lam) (insertPart c mu) := by
  rcases Nat.lt_or_ge c (mu.rowLen 0) with hmu | hmu
  · refine ⟨0, fun j hj => absurd hj (Nat.not_lt_zero j), ?_⟩
    have h1 : mu.rowLen 0 ≤ (insertPart c mu).rowLen 0 :=
      le_rowLen_insertPart_zero_of_mem hc mu (rowLen_zero_mem_rowLens (by omega))
    rw [rowLen_insertPart_zero hc hlam]
    omega
  · obtain ⟨i, hlow, hi⟩ := h
    refine ⟨i + 1, fun j hj => ?_, ?_⟩
    · match j with
      | 0 => rw [rowLen_insertPart_zero hc hlam, rowLen_insertPart_zero hc hmu]
      | j' + 1 =>
        rw [rowLen_insertPart_succ hc hlam, rowLen_insertPart_succ hc hmu]
        exact hlow j' (by omega)
    · rw [rowLen_insertPart_succ hc hlam, rowLen_insertPart_succ hc hmu]
      exact hi

end HJO.Sym
