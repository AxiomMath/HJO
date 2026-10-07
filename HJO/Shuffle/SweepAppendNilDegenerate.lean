/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepAppendNilTwo

/-! # The `α = []` clause of `HJO.Mellit.SweepAppend` fails at `qu = 0` at every `a`, once `A ≥ 2`

`HJO.Mellit.not_sweepAppend_nil_two_three_one_of_q_zero` and
`HJO.Mellit.not_sweepAppend_nil_two_three_one_of_u_zero` (`HJO/Shuffle/SweepAppendTwoThree.lean`)
refute the `α = []` clause at `q = 0` and at `u = 0` at `(a,b) = (2,3)`, `A = 1`, and attribute the
degeneracy to two features of `a ≥ 2`: a type-`C` event with a live north step to its right, whose
operator carries `q⁻¹`, and the letter `𝗓` of the slope word `β_{a,b}`, which carries `(qu)⁻¹`. Both
are absent at `a = 1`, and the docstring of `HJO.Mellit.not_sweepAppend_nil_two_three_one_of_q_zero`
concludes that "at `a = 1` … no negative power of `q` occurs anywhere".

**That conclusion is about `A = 1` only.** At `A ≥ 2` the *field's own scalar*
`(-1)^{(a-1)A}(qu)^{1-A}` has a negative exponent, so in a field it is `0` as soon as `q = 0` or
`u = 0`, at **every** `a` and `b` — no event operator and no slope letter is involved. Hence
`HJO.Mellit.dsc_singleton_eq_zero_of_sweepAppend`: `HJO.Mellit.SweepAppend` forces the invariant of
the one-part composition to vanish identically at `qu = 0`, for every coprime `(a,b)` and every
`A ≥ 2`. That is an infinite family of necessary conditions, each checkable at one parameter point.

The first one that can be checked is `(a,b) = (1,2)`, `A = 2`, where the two paths of
`HJO.Mellit.aboveReturnPaths_one_two_two` are evaluated in
`HJO/Shuffle/SweepAppendNilTwo.lean`, and it FAILS both times:

* at `q = 0` the path `HJO.Paths.tailEx1` is annihilated — its type-`C` event at `(0,2)` has
  `HJO.Paths.sweepRight tailEx1 (0,2) = 1`, so a live north step to its right and a `q⁻¹` in its
  operator, **at `a = 1`** — while `HJO.Paths.tailEx2` hugs the wall, has no such event, and
  survives with `uy_1^4 ≠ 0` (`HJO.Mellit.dsc_one_two_two_q_zero`);
* at `u = 0` it is the other way round: `tailEx2`'s type-`E` event contributes the factor `0` and
  `tailEx1` survives with `-e_1y_1^3 ≠ 0` (`HJO.Mellit.dsc_one_two_two_u_zero`).

So `q ≠ 0` and `u ≠ 0` are REAL exclusions at `a = 1`, not artefacts of the proof of
`HJO.Mellit.sweepAppend_nil_one_two_two` — which is why that theorem carries them and
`HJO.Mellit.sweepAppend_nil_one_one_b`, at `A = 1`, does not.

## `HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc` does not reach this sum

`HJO/Shuffle/SweepAppendOneB.lean` says of the multi-path sum that it "is the content of
`HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc`". It is not, and `HJO.Mellit.Rem41`
(`HJO/Shuffle/Mellit.lean`) is a theorem, so the claim can be checked directly.
Three independent reasons, each fatal:

1. **Wrong ambient object.** `Rem41`'s two sides live in `𝒫 = HJO.Sym.AlphabetSeries L`, reached
   through a realisation `ι`; its right-hand side is `u^{N-ℓ} • ι(proj(d_-^ℓ(D_{η,c_α})))`. The
   `proj` of `HJO.Mellit.sweepWitness` is `MvPolynomial.lcoeff _ 0`
   (`HJO/Shuffle/SweepWitness.lean`) and `ℓ = 1` at `α = [A]`, so `Rem41` constrains only
   the image of `D` under `ι ∘ lcoeff 0 ∘ d_-^{(1)}`, a single element of `Λ`. The `α = []`
   clause is an identity in `HJO.Sweep.Total L`, between two elements of `HJO.Sweep.piece L 1` —
   at `(a,b) = (1,2)`, `A = 2` they are `-e_1y_1^3 + uy_1^4` — and `d_-^{(1)} : V_1 → V_0`
   collapses all of `Λ[y_1]` onto `Λ`.
2. **Wrong direction.** `Rem41` *transports*: `HJO.Mellit.rem41_of_sweepComputes` proves it by
   rewriting the sum of characters into `ι(proj(d_-^ℓ(dsc …)))`, consuming
   `HJO.Mellit.dsc_compColouring_eq_sum_partialSweepWord` and `HJO.Mellit.sweepWord_vac_eq`. It
   reads the character sum *off* the word sum; it computes no word sum.
3. **No stage on the other side.** `Rem41` mentions no replication family, no
   `HJO.Mellit.stageTotal`, no `HJO.Mellit.appendHeights`. The right-hand side of the `α = []`
   clause is `Ω(2;a,b)^{A-1}Ω(1;a,b)(1)` (`HJO.Mellit.dsc_singleton_of_sweepAppend`), and nothing
   in `Rem41` can produce it.

A fourth reason is decisive on its own and needs no reading of the two files: the docstring of
`HJO.Mellit.rem41_of_sweepComputes` (`HJO/Shuffle/MellitRem41.lean`) records that the
derivation spends **no genericity** — "the statement holds at `q = 0`, at `u = 0` and at every root
of unity". The `α = []` clause is false at `q = 0` and at `u = 0` (below, and at `(2,3)` already),
so no genericity-free implication from `Rem41` to it can exist.

The statement whose content the multi-path sum *is* is `HJO.Mellit.mellitInduction_sweepWitness`
(`HJO.Mellit.MellitInduction`), to which `HJO.Mellit.SweepAppend` is equivalent at the witness by
`HJO.Mellit.mellitInduction_sweepWitness_iff_sweepAppend`. `Rem41` sits downstream of it.
-/

@[expose] public section

namespace HJO.Mellit

open HJO.Sweep HJO.Sym HJO.Paths Finset

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {a b : ℕ}

/-! ### The scalar of the append clause, at `qu = 0` -/

omit [Algebra ℚ L] in
/-- **The scalar of the `append` field vanishes at `qu = 0` once `2 ≤ A`.** `(qu)^{1-A}` has a
negative exponent there, and `0⁻¹ = 0` in a field. Nothing about `a`, `b`, the event operators or
the slope word enters: this is the field axioms alone. -/
theorem append_scalar_eq_zero (a : ℕ) {A : ℕ} (hA : 2 ≤ A) (hqu : q * u = 0) :
    (-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ)) = 0 := by
  have hA' : (2 : ℤ) ≤ (A : ℤ) := by exact_mod_cast hA
  rw [hqu, zero_zpow _ (by omega), mul_zero]

/-- **`HJO.Mellit.SweepAppend` forces the invariant of a one-part composition to vanish at
`qu = 0`**, for every coprime `(a,b)` with `a, b > 0` and every `A ≥ 2`. The `α = []` clause reads
`D_{η,c_{(A)}} = (-1)^{(a-1)A}(qu)^{1-A}Ω(2;a,b)^{A-1}Ω(1;a,b)(1)` in closed form
(`HJO.Mellit.dsc_singleton_of_sweepAppend`), and `HJO.Mellit.append_scalar_eq_zero` kills the scalar
however the stage evaluates.

So the clause is refuted at any parameter point with `A ≥ 2` and `qu = 0` at which the sweep side is
nonzero, and this is the statement to check there. It is what
`HJO.Mellit.not_sweepAppend_one_two_of_q_zero` and `HJO.Mellit.not_sweepAppend_one_two_of_u_zero`
check at `(a,b) = (1,2)`, `A = 2` — parameters at which the mechanism of
`HJO.Mellit.not_sweepAppend_nil_two_three_one_of_q_zero`, which needs `2 ≤ a`, is unavailable. -/
theorem dsc_singleton_eq_zero_of_sweepAppend (h : SweepAppend q u a b) (hab : Nat.Coprime a b)
    (ha : 0 < a) (hb : 0 < b) {A : ℕ} (hA : 2 ≤ A) (hqu : q * u = 0) :
    dsc q u a b A (sepLevel a A) (compColouring a b [A]) = 0 := by
  rw [dsc_singleton_of_sweepAppend h hab ha hb (show 0 < A by omega),
    append_scalar_eq_zero a hA hqu, zero_smul]

/-! ### The sweep side at `(a,b) = (1,2)`, `A = 2`, at `q = 0` and at `u = 0` -/

/-- **At `q = 0` the path `HJO.Paths.tailEx1` is annihilated, at `a = 1`.** Its type-`C` event at
`(0,2)` has `HJO.Paths.sweepRight tailEx1 (0,2) = 1` — a live north step to its right, in the
`2 × 4` rectangle — so its operator carries `q⁻¹`. The feature the `(2,3)` refutation attributes to
`2 ≤ a` is therefore present at `a = 1` as soon as `A ≥ 2`; what `A = 1` and `a = 1` have is
`HJO.Mellit.sweepRight_baseOne_of_lt`, a statement about the single path of that rectangle. -/
theorem partialSweepWord_tailEx1_apply_one_q_zero (u : L) :
    partialSweepWord (0 : L) u tailEx1 (sepLevel 1 2) (1 : Total L) = 0 := by
  rw [partialSweepWord_tailEx1 (0 : L) u]
  simp only [Module.End.mul_apply, Module.End.one_apply, zpow_neg_one, inv_zero, zero_smul,
    LinearMap.zero_apply, map_zero]

/-- **`D_{5/2,c_{(2)}} = uy_1^4` at `q = 0`**, the wall-hugging path `HJO.Paths.tailEx2` alone. Its
word is three corner events of width `1`, one type-`E` event and one type-`D` event, none of them
carrying a negative power of `q`, so `q = 0` does not touch it. -/
theorem dsc_one_two_two_q_zero (u : L) :
    dsc (0 : L) u 1 2 2 (sepLevel 1 2) (compColouring 1 2 [2])
      = scal u * (MvPolynomial.X 0 : Total L) ^ 4 := by
  have hne : tailEx1 ≠ tailEx2 := by decide
  rw [dsc_compColouring_eq_sum_partialSweepWord (0 : L) u (isAdmissibleLevel_sepLevel 1 2)
      (separatesDiagonal_sepLevel' 1 2 2) (by decide) (by omega) (by omega)
      (by simp) (by simp),
    aboveReturnPaths_one_two_two, Finset.sum_insert (by simpa using hne), Finset.sum_singleton,
    partialSweepWord_tailEx1_apply_one_q_zero u,
    partialSweepWord_tailEx2_apply_one (0 : L) u (by norm_num), zero_add]

/-- **`D_{5/2,c_{(2)}} = -e_1y_1^3` at `u = 0`**, for `q ∉ {0,1}`: the other way round. The type-`E`
event of `HJO.Paths.tailEx2` contributes the factor `u`, so that path dies, and `HJO.Paths.tailEx1`
— whose word has no `u` in it — survives. Read off
`HJO.Mellit.dsc_one_two_two`, which is uniform in `u`. -/
theorem dsc_one_two_two_u_zero (q : L) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    dsc q (0 : L) 1 2 2 (sepLevel 1 2) (compColouring 1 2 [2])
      = -(MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 : Total L) ^ 3) := by
  rw [dsc_one_two_two q (0 : L) hq0 hq1, scal_zero, zero_mul, add_zero]

/-! ### The refutations -/

/-- **The `α = []`, `A = 2`, `(a,b) = (1,2)` clause is FALSE at `q = 0`, for every `u ≠ 0`**, in the
verbatim shape of the `append` field of `HJO.Mellit.SweepAppend`. The right-hand side is zero for
the scalar's sake alone (`HJO.Mellit.append_scalar_eq_zero`), and the left is `uy_1^4`.

This refutes the `hzero` hypothesis of `HJO.Mellit.sweepAppend_of_forall_band` at `a = 1`, where the
`(2,3)` refutation's mechanism does not apply, and so shows that the `q ≠ 0` of
`HJO.Mellit.sweepAppend_nil_one_two_two` is a real exclusion and not an artefact. -/
theorem not_sweepAppend_nil_one_two_two_of_q_zero (u : L) (hu : u ≠ 0) :
    dsc (0 : L) u 1 2 (([] : List ℕ).sum + 2) (sepLevel 1 (([] : List ℕ).sum + 2))
        (compColouring 1 2 ([] ++ [2]))
      ≠ ((-1 : L) ^ ((1 - 1) * 2) * ((0 : L) * u) ^ (1 - ((2 : ℕ) : ℤ))) •
          stageTotal (0 : L) u 1 2 ([] : List ℕ).length 2
            (dsc (0 : L) u 1 2 ([] : List ℕ).sum (sepLevel 1 ([] : List ℕ).sum)
              (compColouring 1 2 ([] : List ℕ))) := by
  have hnz : (scal u * (MvPolynomial.X 0 : Total L) ^ 4) ≠ 0 := by
    refine mul_ne_zero ?_ (pow_ne_zero 4 (MvPolynomial.X_ne_zero 0))
    rw [scal]
    exact MvPolynomial.C_ne_zero.2 (MvPolynomial.C_ne_zero.2 hu)
  simp only [List.sum_nil, List.length_nil, List.nil_append, Nat.zero_add]
  rw [append_scalar_eq_zero (L := L) 1 (A := 2) le_rfl (zero_mul u), zero_smul,
    dsc_one_two_two_q_zero u]
  exact hnz

/-- **The same clause is FALSE at `u = 0`, for every `q ∉ {0,1}`.** The scalar dies for the same
reason, and the sweep side is `-e_1y_1^3`. So the `u ≠ 0` of
`HJO.Mellit.sweepAppend_nil_one_two_two` is real as well, and together with
`HJO.Mellit.not_sweepAppend_one_left` at `q = 1` this accounts for all three of its hypotheses. -/
theorem not_sweepAppend_nil_one_two_two_of_u_zero (q : L) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    dsc q (0 : L) 1 2 (([] : List ℕ).sum + 2) (sepLevel 1 (([] : List ℕ).sum + 2))
        (compColouring 1 2 ([] ++ [2]))
      ≠ ((-1 : L) ^ ((1 - 1) * 2) * (q * (0 : L)) ^ (1 - ((2 : ℕ) : ℤ))) •
          stageTotal q (0 : L) 1 2 ([] : List ℕ).length 2
            (dsc q (0 : L) 1 2 ([] : List ℕ).sum (sepLevel 1 ([] : List ℕ).sum)
              (compColouring 1 2 ([] : List ℕ))) := by
  have hnz : (MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 : Total L) ^ 3) ≠ 0 := by
    refine mul_ne_zero ?_ (pow_ne_zero 3 (MvPolynomial.X_ne_zero 0))
    rw [elemSymm_one_eq_X]
    exact MvPolynomial.C_ne_zero.2 (MvPolynomial.X_ne_zero 0)
  simp only [List.sum_nil, List.length_nil, List.nil_append, Nat.zero_add]
  rw [append_scalar_eq_zero (L := L) 1 (A := 2) le_rfl (mul_zero q), zero_smul,
    dsc_one_two_two_u_zero q hq0 hq1]
  exact neg_ne_zero.2 hnz

/-- **`HJO.Mellit.SweepAppend` is false at `q = 0`, `(a,b) = (1,2)`, for every `u ≠ 0`.** Its
`α = []`, `A = 2` instance is `HJO.Mellit.not_sweepAppend_nil_one_two_two_of_q_zero`. -/
theorem not_sweepAppend_one_two_of_q_zero (u : L) (hu : u ≠ 0) : ¬ SweepAppend (0 : L) u 1 2 :=
  fun h => not_sweepAppend_nil_one_two_two_of_q_zero u hu
    (h [] 2 (List.forall_mem_nil _) (by omega))

/-- **`HJO.Mellit.SweepAppend` is false at `u = 0`, `(a,b) = (1,2)`, for every `q ∉ {0,1}`.** -/
theorem not_sweepAppend_one_two_of_u_zero (q : L) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    ¬ SweepAppend q (0 : L) 1 2 :=
  fun h => not_sweepAppend_nil_one_two_two_of_u_zero q hq0 hq1
    (h [] 2 (List.forall_mem_nil _) (by omega))

/-! ### The refutations, applied to `hzero` verbatim

`HJO.Mellit.dsc_singleton_of_hzero` reads the `hzero` hypothesis of
`HJO.Mellit.sweepAppend_of_forall_band` in `HJO.Mellit.dsc` form, so that the two refutations above
refute `hzero` itself rather than the conjunction `hzero ∧ hband`. No singleton claim about
`HJO.Mellit.aboveReturnPaths a b 0 []` is needed: the stage is linear, so the sum over base paths on
the right collapses against `HJO.Mellit.dsc_empty_eq_one`. -/

/-- **The `hzero` hypothesis of `HJO.Mellit.sweepAppend_of_forall_band`, in `HJO.Mellit.dsc` form.**
At `α = []` the outer index set is `HJO.Mellit.aboveReturnPaths a b 0 []` and
`HJO.Mellit.sum_aboveReturnPaths_append_singleton` turns the per-path left-hand sides into the
single sum over `HJO.Mellit.aboveReturnPaths a b A ([] ++ [A])`, which is
`HJO.Mellit.dsc_compColouring_eq_sum_partialSweepWord`. On the right the scalar and
`HJO.Mellit.stageTotal` are linear, so summing over base paths puts the whole sum inside the stage,
where it is `1` by `HJO.Mellit.dsc_empty_eq_one`. So `hzero` says exactly what
`HJO.Mellit.dsc_singleton_of_sweepAppend` says, one `A` at a time. -/
theorem dsc_singleton_of_hzero (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (hzero : ∀ (α : List ℕ) (A : ℕ), (∀ x ∈ α, 0 < x) → 0 < A → α.sum = 0 →
      ∀ z ∈ aboveReturnPaths a b α.sum α,
        ∑ w ∈ aboveReturnPaths a b A [A],
            partialSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) (1 : Total L)
          = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
              stageTotal q u a b α.length A
                (partialSweepWord q u z (sepLevel a α.sum) (1 : Total L)))
    {A : ℕ} (hA : 0 < A) :
    dsc q u a b (0 + A) (sepLevel a (0 + A)) (compColouring a b (([] : List ℕ) ++ [A]))
      = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
          stageTotal q u a b 0 A (1 : Total L) := by
  have hc : compColouring a b ([] : List ℕ) = (∅ : Finset (ℕ × ℕ)) := by simp [compColouring]
  have hbase : ∑ z ∈ aboveReturnPaths a b 0 ([] : List ℕ),
      partialSweepWord q u z (sepLevel a 0) (1 : Total L) = (1 : Total L) := by
    rw [← dsc_compColouring_eq_sum_partialSweepWord q u (isAdmissibleLevel_sepLevel a 0)
      (separatesDiagonal_sepLevel' a b 0) hab ha hb (by simp) (by simp), hc]
    exact dsc_empty_eq_one q u (isAdmissibleLevel_sepLevel a 0)
      (separatesDiagonal_sepLevel' a b 0) hab ha hb
  have hsplit := sum_aboveReturnPaths_append_singleton (a := a) (b := b) (N := 0) (A := A)
    (α := ([] : List ℕ))
    (f := fun y => partialSweepWord q u y (sepLevel a (0 + A)) (1 : Total L))
  have h0 := hzero [] A (List.forall_mem_nil _) hA List.sum_nil
  simp only [List.sum_nil, List.length_nil] at h0
  rw [dsc_compColouring_eq_sum_partialSweepWord q u (isAdmissibleLevel_sepLevel a (0 + A))
      (separatesDiagonal_sepLevel' a b (0 + A)) hab ha hb (by simpa using hA) (by simp),
    hsplit, Finset.sum_congr rfl h0, ← Finset.smul_sum, ← map_sum, hbase]

/-- **The `hzero` hypothesis of `HJO.Mellit.sweepAppend_of_forall_band` is FALSE at `q = 0`,
`(a,b) = (1,2)`, for every `u ≠ 0`** — verbatim, in the shape that theorem asks for it. So the
`α = []` clause is not merely unreached at `a = 1`: it is false there, once `A ≥ 2`. -/
theorem not_hzero_one_two_of_q_zero (u : L) (hu : u ≠ 0) :
    ¬ (∀ (α : List ℕ) (A : ℕ), (∀ x ∈ α, 0 < x) → 0 < A → α.sum = 0 →
        ∀ z ∈ aboveReturnPaths 1 2 α.sum α,
          ∑ w ∈ aboveReturnPaths 1 2 A [A],
              partialSweepWord (0 : L) u (appendHeights z w) (sepLevel 1 (α.sum + A))
                (1 : Total L)
            = ((-1 : L) ^ ((1 - 1) * A) * ((0 : L) * u) ^ (1 - (A : ℤ))) •
                stageTotal (0 : L) u 1 2 α.length A
                  (partialSweepWord (0 : L) u z (sepLevel 1 α.sum) (1 : Total L))) := by
  intro h
  have hd := dsc_singleton_of_hzero (Nat.coprime_one_left 2) (by omega) (by omega) h
    (A := 2) (by omega)
  simp only [Nat.zero_add, List.nil_append] at hd
  rw [append_scalar_eq_zero (L := L) 1 (A := 2) le_rfl (zero_mul u), zero_smul,
    dsc_one_two_two_q_zero u] at hd
  refine (mul_ne_zero ?_ (pow_ne_zero 4 (MvPolynomial.X_ne_zero 0))) hd
  rw [scal]
  exact MvPolynomial.C_ne_zero.2 (MvPolynomial.C_ne_zero.2 hu)

/-- **The `hzero` hypothesis is FALSE at `u = 0`, `(a,b) = (1,2)`, for every `q ∉ {0,1}`** —
verbatim, likewise. -/
theorem not_hzero_one_two_of_u_zero (q : L) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    ¬ (∀ (α : List ℕ) (A : ℕ), (∀ x ∈ α, 0 < x) → 0 < A → α.sum = 0 →
        ∀ z ∈ aboveReturnPaths 1 2 α.sum α,
          ∑ w ∈ aboveReturnPaths 1 2 A [A],
              partialSweepWord q (0 : L) (appendHeights z w) (sepLevel 1 (α.sum + A))
                (1 : Total L)
            = ((-1 : L) ^ ((1 - 1) * A) * (q * (0 : L)) ^ (1 - (A : ℤ))) •
                stageTotal q (0 : L) 1 2 α.length A
                  (partialSweepWord q (0 : L) z (sepLevel 1 α.sum) (1 : Total L))) := by
  intro h
  have hd := dsc_singleton_of_hzero (Nat.coprime_one_left 2) (by omega) (by omega) h
    (A := 2) (by omega)
  simp only [Nat.zero_add, List.nil_append] at hd
  rw [append_scalar_eq_zero (L := L) 1 (A := 2) le_rfl (mul_zero q), zero_smul,
    dsc_one_two_two_u_zero q hq0 hq1, neg_eq_zero] at hd
  refine (mul_ne_zero ?_ (pow_ne_zero 3 (MvPolynomial.X_ne_zero 0))) hd
  rw [elemSymm_one_eq_X]
  exact MvPolynomial.C_ne_zero.2 (MvPolynomial.X_ne_zero 0)

end HJO.Mellit

end
