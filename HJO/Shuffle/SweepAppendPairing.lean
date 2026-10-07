/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepAppendBandPerPath
public import HJO.Shuffle.HalfTurn

/-! # The per-path residual of the append identity, and why no pairing cancels it

`HJO.Mellit.SweepAppend` is the identity **summed over the base paths**
(`HJO.Mellit.sweepAppend_iff_sum_split`), and the per-path reading of it is false
(`HJO/Shuffle/SweepAppendBandPerPath.lean`). So the sum of the per-path discrepancies
vanishes while no single one does, and the natural next hope is that they cancel *in pairs*: a
sign-reversing involution on `HJO.Mellit.aboveReturnPaths a b α.sum α`.

This file names that residual — `HJO.Mellit.appendDisc` — and reports that **there is no such
involution**, by computation, at four independent instances. The statement it disproves is not
formalised here, on purpose: a reduction of `HJO.Mellit.SweepAppend` to a pairing would be one more
correct theorem with a false hypothesis, which is what `HJO.Mellit.sweepAppend_of_forall_band`,
`HJO.Mellit.sweepAppend_of_forall_band_uniform` and `HJO.Mellit.sweepAppend_of_forall_path` already
are.

## What this file proves

* `HJO.Mellit.appendDisc` — the discrepancy of the append identity at one base path: the tail sum on
  the left minus the staged base word on the right, in `HJO.Mellit.partialSweepWord` alone.
* `HJO.Mellit.sweepAppend_iff_sum_appendDisc` — `HJO.Mellit.SweepAppend` is exactly the vanishing of
  `∑_z` of that discrepancy, one composition at a time. This is
  `HJO.Mellit.sweepAppend_iff_sum_split` with the subtraction done, and it carries the same
  coprimality and positivity and nothing on `q` or `u`.
* `HJO.Mellit.appendDisc_eq_zero_of_eq_neg` — a base path at which the discrepancy is its own
  negative has discrepancy zero. So a sign-reversing map must have **vanishing discrepancy at every
  fixed point**: that is the one necessary condition on a pairing that is parameter-free and
  provable here.
* `HJO.Mellit.not_isBelowDiagonal_of_isAboveDiagonal` and
  `HJO.Mellit.halfTurn_notMem_aboveReturnPaths` — **the half turn is not a pairing on the base
  paths, and cannot be made into one.** For coprime `a`, `b` with `1 < a` and `0 < N` no path is
  both above- and below-diagonal, and `HJO.Paths.isBelowDiagonal_halfTurn` sends an above-diagonal
  path to a below-diagonal one; so `HJO.Paths.halfTurn` maps
  `HJO.Mellit.aboveReturnPaths a b N α` entirely *outside* the above-diagonal paths, for every
  return composition. It is a bijection between the two orientations
  (`HJO.Paths.halfTurn_bijOn`), which is why it serves `HJO.gesselReverseSum` and cannot
  serve here.

## Why no pairing exists: the computation

All of the following is **model-only** — a computer-algebra model outside Lean, validated
against `HJO.Mellit.sweepAppend_nil_two_three_one`,
`HJO.Mellit.sweepAppend_nil_one_two_two`, `HJO.Mellit.dsc_one_two_two`,
`HJO.Mellit.partialSweepWord_tailEx1_apply_one`, `HJO.Mellit.partialSweepWord_tailEx2_apply_one`,
`HJO.Sweep.replOneTotal_two_three` and the `decide`-checked ranks, event types, widths and
`HJO.Paths.sweepRight`s of `HJO/Shuffle/SweepAppendNilTwo.lean`. Computed over `ℚ(q,u)` with
`q` and `u` transcendental, so every inverse stays an honest rational function.

For each instance: `#z` base paths, the rank of the `ℚ(q,u)`-span of the discrepancies, and the
space of linear relations among them.

Column `sub` is whether some proper subset of the base paths has vanishing discrepancy sum.

| `(a,b)` | `α` | `A` | `#z` | `∑_z D(z)` | rank | relations | sub | pairing |
|---|---|---|---|---|---|---|---|---|
| `(2,3)` | `[1]`   | `1` | `2`  | `0` | `1`  | `⟨(1,1)⟩`   | none | forced |
| `(2,3)` | `[1]`   | `2` | `2`  | `0` | `1`  | `⟨(1,1)⟩`   | none | forced |
| `(2,5)` | `[1]`   | `1` | `3`  | `0` | `2`  | `⟨(1,…,1)⟩` | none | **NONE** |
| `(2,3)` | `[1,1]` | `1` | `4`  | `0` | `3`  | `⟨(1,…,1)⟩` | none | **NONE** |
| `(3,4)` | `[1]`   | `1` | `5`  | `0` | `4`  | `⟨(1,…,1)⟩` | none | **NONE** |
| `(2,3)` | `[2]`   | `1` | `19` | `0` | `18` | `⟨(1,…,1)⟩` | none | **NONE** |

The reading is uniform and much stronger than the failure of a pairing. At every instance the
discrepancies are **linearly independent but for the single global relation** `∑_z D(z) = 0`: the
rank is `#z - 1`, the relation space is the line spanned by `(1,…,1)`, no `D(z)` is zero, and no
proper subset of the base paths has vanishing discrepancy sum. Consequently there is

* no sign-reversing involution (a pairing is a `0, ±1` relation supported on two coordinates);
* no partition of the base paths into blocks with vanishing block sums;
* no cancellation among any proper subset, with **any** coefficients at all.

The cancellation is irreducibly global: the whole base-path set has to be summed at once. That is
parameter-free — the rank is `#z - 1` at three independent `(q,u)` specialisations, and since the
all-ones relation holds identically the rank over `ℚ(q,u)` is exactly `#z - 1` and the relation
space is exactly that line. No exclusion on `q` or `u` changes it.

The two `#z = 2` rows carry no information: with two base paths and a vanishing sum the two
discrepancies *are* negatives of each other, whatever the mechanism. The smallest informative
instance is `(2,5)`, `α = [1]`, `A = 1`, with three base paths, and the pairing already fails there.

## Where that leaves the route

`HJO.Mellit.sweepAppend_of_forall_sum_band` remains the form of the band statement that is open, and
by the above nothing weaker than its `∑_z` will do. The residual is therefore a statement about the
**total** `HJO.Mellit.dsc` at a composition, which is what `HJO.Mellit.SweepAppend` literally is,
and the next lead is a closed form for that total rather than a path-by-path or block-by-block
comparison. Two data points, both model-only and both verified exactly at `(a,b) = (2,3)`: writing
`T(α)` for `∑_z` of `HJO.Mellit.partialSweepWord` at `HJO.Mellit.sepLevel a α.sum`,

`T([]) = 1`,  `T([1]) = y₁²(p₁ - u y₁)`,
`T([1,1]) = q y₁²y₂²((p₁ - u y₁)(p₁ - u y₂) + (q-1) e₂)`.

## References

A. Mellit, *Toric braids and `(m, n)`-parking
functions*, sections 4 and 6.
-/

@[expose] public section

namespace HJO.Mellit

open HJO.Sweep HJO.Sym HJO.Paths Finset

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {a b N : ℕ}

/-! ### The residual, one base path at a time -/

/-- **The discrepancy of the append identity at one base path.** The left side of
`HJO.Mellit.sweepAppend_iff_sum_split` summand at `z` — the tail sum of
`HJO.Mellit.partialSweepWord` over the extensions of `z` — minus the right side's summand, the
staged base word. `HJO.Mellit.SweepAppend` is the vanishing of `∑_z` of this and nothing else; the
vanishing of the individual summands is false. -/
noncomputable def appendDisc (q u : L) (a b : ℕ) (α : List ℕ) (A : ℕ) (z : Heights a b α.sum) :
    Total L :=
  (∑ w ∈ aboveReturnPaths a b A [A],
      partialSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) (1 : Total L))
    - ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
        stageTotal q u a b α.length A (partialSweepWord q u z (sepLevel a α.sum) (1 : Total L))

/-- **`HJO.Mellit.SweepAppend` is the vanishing of the summed discrepancy.**
`HJO.Mellit.sweepAppend_iff_sum_split` with the subtraction carried out, so that the residual has a
name and the quantifier `∑_z` sits where it belongs: outside. -/
theorem sweepAppend_iff_sum_appendDisc (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) :
    SweepAppend q u a b ↔ ∀ (α : List ℕ) (A : ℕ), (∀ x ∈ α, 0 < x) → 0 < A →
      ∑ z ∈ aboveReturnPaths a b α.sum α, appendDisc q u a b α A z = 0 := by
  rw [sweepAppend_iff_sum_split hab ha hb]
  simp only [appendDisc, Finset.sum_sub_distrib, sub_eq_zero]

/-! ### What a sign-reversing pairing would have to satisfy -/

/-- **A base path whose discrepancy is its own negative has discrepancy zero.** `HJO.Sweep.Total L`
is a `ℚ`-module, so it has no `2`-torsion. Hence a sign-reversing map on the base paths must have
vanishing discrepancy at each of its fixed points — and by the module docstring's computation no
base path has vanishing discrepancy, at any of the four instances tested. -/
theorem appendDisc_eq_zero_of_eq_neg {α : List ℕ} {A : ℕ} {z : Heights a b α.sum}
    (h : appendDisc q u a b α A z = -appendDisc q u a b α A z) :
    appendDisc q u a b α A z = 0 := by
  set d : Total L := appendDisc q u a b α A z with hd
  have h2 : (2 : ℚ) • d = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel d
  calc d = ((2 : ℚ)⁻¹ * (2 : ℚ)) • d := by norm_num
    _ = (2 : ℚ)⁻¹ • ((2 : ℚ) • d) := mul_smul _ _ _
    _ = 0 := by rw [h2]; simp

/-! ### The half turn is not a pairing on the base paths

The half turn is the library's one involution on height vectors, and it is a bijection between
the two orientations (`HJO.Paths.halfTurn_bijOn`), not a self-map of either. The two lemmas below
say that in the form the pairing question needs: outside the degenerate parameters no path is both
above- and below-diagonal, so the half turn of a base path is not a base path, for any return
composition. -/

/-- **No path is both above- and below-diagonal**, once `a` and `b` are coprime with `1 < a` and the
rectangle is nonempty. Both conditions together force `a ŷ_r = b r` at every `r ≤ aN`; at `r = 1`
that is `a ∣ b`, and with `HJO.Nat.Coprime` that gives `a = 1`. -/
@[hjo "not_sweep_append_half_turn"]
theorem not_isBelowDiagonal_of_isAboveDiagonal (hab : Nat.Coprime a b) (ha : 1 < a) (hN : 0 < N)
    {y : Heights a b N} (hy : IsAboveDiagonal y) : ¬IsBelowDiagonal y := by
  intro hy'
  have h1 : 1 ≤ a * N := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hup : b * 1 ≤ a * ht y 1 := hy.2.2.2 1 h1
  have hdown : a * ht y 1 ≤ b * 1 := hy'.2.2.2 1 h1
  have heq : a * ht y 1 = b := by omega
  have hdvd : a ∣ b := ⟨ht y 1, heq.symm⟩
  have : a = 1 := Nat.Coprime.eq_one_of_dvd hab hdvd
  omega

/-- **The half turn of a base path is never a base path.** `HJO.Paths.isBelowDiagonal_halfTurn`
sends an above-diagonal path to a below-diagonal one, and by
`HJO.Mellit.not_isBelowDiagonal_of_isAboveDiagonal` nothing is both. So `HJO.Paths.halfTurn` leaves
`HJO.Mellit.aboveReturnPaths a b N α` for good, whatever return composition one lands it in, and it
is not the pairing the append residual would need. -/
@[hjo "not_sweep_append_half_turn"]
theorem halfTurn_notMem_aboveReturnPaths (hab : Nat.Coprime a b) (ha : 1 < a) (hN : 0 < N)
    {α β : List ℕ} {z : Heights a b N} (hz : z ∈ aboveReturnPaths a b N α) :
    halfTurn z ∉ aboveReturnPaths a b N β := by
  intro hmem
  exact not_isBelowDiagonal_of_isAboveDiagonal hab ha hN (mem_aboveReturnPaths_iff.1 hmem).1
    (isBelowDiagonal_halfTurn (mem_aboveReturnPaths_iff.1 hz).1)

end HJO.Mellit

end
